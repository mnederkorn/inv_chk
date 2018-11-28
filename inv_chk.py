from z3 import *
import cores
import os
import re
from tempfile import TemporaryFile, _TemporaryFileWrapper

class Rule:

	def __init__(self, s):

		graph_re = r"(\n(    |\t)*\d+( \d+)*(\n(    |\t)*\d+ \d+ [A-Z]+)*)"
		morph_re = r"\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*"

		regex = re.fullmatch(r"\n(    |\t)*I:(?P<I>{})\n(    |\t)*L:(?P<L>{})\n(    |\t)*R:(?P<R>{})\n(    |\t)*morphL:(?P<morphL>{})\n(    |\t)*morphR:(?P<morphR>{})".format(graph_re, graph_re, graph_re, morph_re,  morph_re, ), s, flags=re.DOTALL)

		i = regex.group("I").lstrip("\n")
		i = re.compile("(    |\t)").sub("", i)
		i_file = TemporaryFile(mode="w+")
		i_file.write(i)
		i_file.seek(0)

		self.i = cores.Graph(parse=i_file)

		l = regex.group("L").lstrip("\n")
		l = re.compile("(    |\t)").sub("", l)
		l_file = TemporaryFile(mode="w+")
		l_file.write(l)
		l_file.seek(0)

		self.l = cores.Graph(parse=l_file)

		r = regex.group("R").lstrip("\n")
		r = re.compile("(    |\t)").sub("", r)
		r_file = TemporaryFile(mode="w+")
		r_file.write(r)
		r_file.seek(0)

		self.r = cores.Graph(parse=r_file)

		L_V = re.findall(r"\d+->\d+", regex.group("morphL"))
		R_V = re.findall(r"\d+->\d+", regex.group("morphR"))
		L_E = re.findall(r"\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+", regex.group("morphL"))
		R_E = re.findall(r"\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+", regex.group("morphR"))

		L_V = [n.split("->") for n in L_V]
		R_V = [n.split("->") for n in R_V]
		L_E = [n.split("->") for n in L_E]
		R_E = [n.split("->") for n in R_E]

		L_E = [[".".join(m.split()) for m in n] for n in L_E]
		R_E = [[".".join(m.split()) for m in n] for n in R_E]

		self.l_v = {n[0]: n[1] for n in L_V}
		self.r_v = {n[0]: n[1] for n in R_V}
		self.l_e = {n[0]: n[1] for n in L_E}
		self.r_e = {n[0]: n[1] for n in R_E}

class Inv_Chk:

	def __init__(self, file):

		rule = open(file, "r").read()

		graph_re = r"\n(    |\t)*\d+( \d+)*(\n(    |\t)*\d+ \d+ [A-Z]+)*"
		rule_re = r"(\n(    |\t)*rule\d+:\n(    |\t)*I:{}\n(    |\t)*L:{}\n(    |\t)*R:{}\n(    |\t)*morphL:\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*\n(    |\t)*morphR:\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*)+".format(graph_re, graph_re, graph_re)

		regex = re.fullmatch(r"T:(?P<T>{})\nrules:(?P<rules>{})".format(graph_re, rule_re), rule, flags=re.DOTALL)

		t = regex.group("T").lstrip("\n")
		t = re.compile("(    |\t)").sub("", t)
		t_file = TemporaryFile(mode="w+")
		t_file.write(t)
		t_file.seek(0)

		t = cores.Graph(parse=t_file)

		t.solve()

		self.core_t = t

		self.rules = {}

		for n in re.split(r"\n(?:    |\t)rule", regex.group("rules"))[1:]:
			rule = re.fullmatch(r"(\d+):(\n.*)", n, flags=re.DOTALL)
			self.rules[rule[1]] = Rule(rule[2])

		for n in self.rules:
			t_l = find_morphism(self.rules[n].l.graph, self.core_t.graph)
			t_r = find_morphism(self.rules[n].r.graph, self.core_t.graph)

			for m in t_l:
				if not any([all([m[0][self.rules[n].l_v[k]]==l[0][self.rules[n].r_v[k]]	for k in self.rules[n].i.graph]) and
					all([m[1][self.rules[n].l_e[k]]==l[1][self.rules[n].r_e[k]] for k in [".".join((j,h,i)) for j in self.rules[n].i.graph for h in self.rules[n].i.graph[j] for i in self.rules[n].i.graph[j][h]]]) for l in t_r]):
					print("The type graph language L(T) is not closed under the set of rules. Under Rule {}, there is no fitting t_R for t_L: {}".format(n,pprint_morphism(m)))
					return
		
		print("The type graph language L(T) is closed under the set of rules. In every rule for every t_L there exists a fitting right-hand side counterpart t_R.")

def pprint_morphism(tpl):

	phi_v = ", ".join(["{}->{}".format(n, tpl[0][n]) for n in tpl[0]])
	phi_e = ", ".join(["{}->{}".format(n, tpl[1][n]) for n in tpl[1]])

	return "t_L_V: ({}), t_L_E: ({})".format(phi_v, phi_e)

def find_morphism(L, T):

	cntxt = Context()

	s = Solver(ctx=cntxt)

	V_L = Datatype("V_L", ctx=cntxt)
	for n in [n for n in L]:
		V_L.declare(n)
	V_L = V_L.create()

	V_T = Datatype("V_T", ctx=cntxt)
	for n in [n for n in T]:
		V_T.declare(n)
	V_T = V_T.create()

	La = Datatype("L", ctx=cntxt)
	for n in {l for n in L for m in L[n] for l in L[n][m]}|{l for n in T for m in T[n] for l in T[n][m]}:
		La.declare(n)
	La = La.create()

	E_L = Datatype("E_L", ctx=cntxt)
	for n in [(n,m,l) for n in L for m in L[n] for l in L[n][m]]:
		E_L.declare(".".join(n))
	E_L = E_L.create()

	src_L = Function("src_L", E_L, V_L)
	tgt_L = Function("tgt_L", E_L, V_L)
	lab_L = Function("lab_L", E_L, La)

	for n in [(n,m,l) for n in L for m in L[n] for l in L[n][m]]:
		s.add(src_L(getattr(E_L, ".".join(n))) == getattr(V_L, n[0]))
		s.add(tgt_L(getattr(E_L, ".".join(n))) == getattr(V_L, n[1]))
		s.add(lab_L(getattr(E_L, ".".join(n))) == getattr(La, n[2]))

	E_T = Datatype("E_T", ctx=cntxt)
	for n in [(n,m,l) for n in T for m in T[n] for l in T[n][m]]:
		E_T.declare(".".join(n))
	E_T = E_T.create()

	src_T = Function("src_T", E_T, V_T)
	tgt_T = Function("tgt_T", E_T, V_T)
	lab_T = Function("lab_T", E_T, La)

	for n in [(n,m,l) for n in T for m in T[n] for l in T[n][m]]:
		s.add(src_T(getattr(E_T, ".".join(n))) == getattr(V_T, n[0]))
		s.add(tgt_T(getattr(E_T, ".".join(n))) == getattr(V_T, n[1]))
		s.add(lab_T(getattr(E_T, ".".join(n))) == getattr(La, n[2]))

	phi_V = Function("phi_V", V_L, V_T)
	phi_E = Function("phi_E", E_L, E_T)

	for n in [(n,m,l) for n in L for m in L[n] for l in L[n][m]]:
		s.add(phi_V(src_L(getattr(E_L, ".".join(n))))==src_T(phi_E(getattr(E_L, ".".join(n)))))
		s.add(phi_V(tgt_L(getattr(E_L, ".".join(n))))==tgt_T(phi_E(getattr(E_L, ".".join(n)))))
		s.add(lab_L(getattr(E_L, ".".join(n)))==lab_T(phi_E(getattr(E_L, ".".join(n)))))

	mappings = []

	while True:

		if s.check()==sat:

			m = s.model()

			v = {getattr(V_L, n): m.eval(phi_V(getattr(V_L, n))) for n in L}
			e = {getattr(E_L, n): m.eval(phi_E(getattr(E_L, n))) for n in [".".join((n,m,l)) for n in L for m in L[n] for l in L[n][m]]}

			v_s = {str(n):str(v[n]) for n in v}
			e_s = {str(n):str(e[n]) for n in e}

			mappings.append((v_s,e_s))

			deny = []

			for n in v:
				deny.append(phi_V(n)==v[n])
			for n in e:
				deny.append(phi_E(n)==e[n])

			s.add(Not(And(deny, cntxt), cntxt))

		else:

			break

	return mappings

if __name__ == '__main__':

	assert len(sys.argv) == 2
	assert type(sys.argv[1]) == str and os.path.isfile(sys.argv[1])

	ic = Inv_Chk(sys.argv[1])