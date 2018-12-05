from z3 import *
import cores
import os
import re
import math

from tempfile import TemporaryFile, _TemporaryFileWrapper
from tkinter import *
from tkinter import filedialog
from tkinter import messagebox
from tkinter import ttk
from datetime import datetime
from graphviz import Digraph
from PIL import Image, ImageTk

zoom_factor = (2**(1/2))

class Rule:

    def __init__(self, s, n):

        graph_re = r"(\n(    |\t)*\d+( \d+)*(\n(    |\t)*\d+ \d+ [A-Z]+)*)"
        morph_re = r"\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*"

        regex = re.fullmatch(r"\n(    |\t)*I:(?P<I>{})\n(    |\t)*L:(?P<L>{})\n(    |\t)*R:(?P<R>{})\n(    |\t)*morphL:(?P<morphL>{})\n(    |\t)*morphR:(?P<morphR>{})".format(graph_re, graph_re, graph_re, morph_re,  morph_re, ), s, flags=re.DOTALL)

        if regex == None:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The content does not match the required syntax.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe content does not match the required syntax.".format(n))
                raise

        i = regex.group("I").lstrip("\n")
        i = re.compile("(    |\t)").sub("", i)
        i_file = TemporaryFile(mode="w+")
        i_file.write(i)
        i_file.seek(0)

        try:
            self.i = cores.Graph(parse=i_file)
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing graph I.")
                print(e)
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing graph I.\n"+str(e))
                raise

        l = regex.group("L").lstrip("\n")
        l = re.compile("(    |\t)").sub("", l)
        l_file = TemporaryFile(mode="w+")
        l_file.write(l)
        l_file.seek(0)

        try:
            self.l = cores.Graph(parse=l_file)
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing graph L.")
                print(e)
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing graph L.\n"+str(e))
                raise

        r = regex.group("R").lstrip("\n")
        r = re.compile("(    |\t)").sub("", r)
        r_file = TemporaryFile(mode="w+")
        r_file.write(r)
        r_file.seek(0)

        try:
            self.r = cores.Graph(parse=r_file)
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing graph R.")
                print(e)
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing graph R.\n"+str(e))
                raise

        L_V = re.findall(r"\d+->\d+", regex.group("morphL"))
        R_V = re.findall(r"\d+->\d+", regex.group("morphR"))
        L_E = re.findall(r"\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+", regex.group("morphL"))
        R_E = re.findall(r"\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+", regex.group("morphR"))

        L_V = [n.split("->") for n in L_V]
        R_V = [n.split("->") for n in R_V]
        L_E = [n.split("->") for n in L_E]
        R_E = [n.split("->") for n in R_E]

        L_E = [[m.split() for m in n] for n in L_E]
        R_E = [[m.split() for m in n] for n in R_E]

        try:
            assert sorted([n for n in self.i.graph])==sorted([n[0] for n in L_V])
            assert sorted([[n,m,l] for n in self.i.graph for m in self.i.graph[n] for l in self.i.graph[n][m]])==sorted([n[0] for n in L_E])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The domain of the function phi_L has to be exactly equal to the elements of I.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe domain of the function phi_L has to be exactly equal to the elements of I.".format(n))
                raise

        try:
            assert sorted([n for n in self.i.graph])==sorted([n[0] for n in R_V])
            assert sorted([[n,m,l] for n in self.i.graph for m in self.i.graph[n] for l in self.i.graph[n][m]])==sorted([n[0] for n in R_E])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The domain of the function phi_R has to be exactly equal to the elements of I.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe domain of the function phi_R has to be exactly equal to the elements of I.".format(n))
                raise

        try:
            l_edges = [[n,m,l] for n in self.l.graph for m in self.l.graph[n] for l in self.l.graph[n][m]]
            assert all([n[1] in self.l.graph for n in L_V])
            assert all([n[1] in l_edges for n in L_E])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The image of the function phi_L has to a subset of the elements of L.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe image of the function phi_L has to a subset of the elements of L.".format(n))
                raise

        try:
            r_edges = [[n,m,l] for n in self.r.graph for m in self.r.graph[n] for l in self.r.graph[n][m]]
            assert all([n[1] in self.r.graph for n in R_V])
            assert all([n[1] in r_edges for n in R_E])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The image of the function phi_R has to a subset of the elements of R.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe image of the function phi_R has to a subset of the elements of R.".format(n))
                raise

        try:
            i_edges = [(n,m,l) for n in self.i.graph for m in self.i.graph[n] for l in self.i.graph[n][m]]
            v_map = {n[0]: n[1] for n in L_V}
            e_map = {tuple(n[0]): n[1] for n in L_E}
            assert all([v_map[n[0]]==e_map[n][0] and v_map[n[1]]==e_map[n][1] and n[2]==e_map[n][2] for n in i_edges])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The function phi_L is not a morphism.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe function phi_L is not a morphism.".format(n))
                raise

        try:
            i_edges = [(n,m,l) for n in self.i.graph for m in self.i.graph[n] for l in self.i.graph[n][m]]
            v_map = {n[0]: n[1] for n in R_V}
            e_map = {tuple(n[0]): n[1] for n in R_E}
            assert all([v_map[n[0]]==e_map[n][0] and v_map[n[1]]==e_map[n][1] and n[2]==e_map[n][2] for n in i_edges])
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing rule {}.".format(n))
                print("The function phi_R is not a morphism.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing rule {}.\nThe function phi_R is not a morphism.".format(n))
                raise

        L_E = [[".".join(m) for m in n] for n in L_E]
        R_E = [[".".join(m) for m in n] for n in R_E]

        self.l_v = {n[0]: n[1] for n in L_V}
        self.r_v = {n[0]: n[1] for n in R_V}
        self.l_e = {n[0]: n[1] for n in L_E}
        self.r_e = {n[0]: n[1] for n in R_E}

class Inv_Chk:

    def __init__(self, file):

        file = open(file, "r")

        rule = file.read()

        file.close()

        graph_re = r"\n(    |\t)*\d+( \d+)*(\n(    |\t)*\d+ \d+ [A-Z]+)*"
        rule_re = r"(\n(    |\t)*rule\d+:\n(    |\t)*I:{}\n(    |\t)*L:{}\n(    |\t)*R:{}\n(    |\t)*morphL:\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*\n(    |\t)*morphR:\n(    |\t)*V:(\n(    |\t)*\d+->\d+)+\n(    |\t)*E:(\n(    |\t)*\d+ \d+ [A-Z]+->\d+ \d+ [A-Z]+)*)+".format(graph_re, graph_re, graph_re)

        regex = re.fullmatch(r"T:(?P<T>{})\nrules:(?P<rules>{})".format(graph_re, rule_re), rule, flags=re.DOTALL)

        if regex == None:
            if len(sys.argv) > 1:
                print("There has been an Error parsing the rule.")
                print("The content of the input file does not match the required syntax.")
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing the rule.")
                raise

        t = regex.group("T").lstrip("\n")
        t = re.compile("(    |\t)").sub("", t)
        t_file = TemporaryFile(mode="w+")
        t_file.write(t)
        t_file.seek(0)

        try:
            t = cores.Graph(parse=t_file)
        except Exception as e:
            if len(sys.argv) > 1:
                print("There has been an Error parsing graph T.")
                print(e)
                exit()
            else:
                messagebox.showerror("", "There has been an Error parsing graph T.\n"+str(e))
                raise

        t.solve()

        self.core_t = t

        self.rules = {}

        for n in re.split(r"\n(?:    |\t)rule", regex.group("rules"))[1:]:
            rule = re.fullmatch(r"(\d+):(\n.*)", n, flags=re.DOTALL)
            self.rules[rule[1]] = Rule(rule[2], rule[1])

    def check_inv(self):

        for n in self.rules:
            t_l = find_morphism(self.rules[n].l.graph, self.core_t.graph)
            t_r = find_morphism(self.rules[n].r.graph, self.core_t.graph)

            for m in t_l:
                if not any([all([m[0][self.rules[n].l_v[k]]==l[0][self.rules[n].r_v[k]]    for k in self.rules[n].i.graph]) and
                    all([m[1][self.rules[n].l_e[k]]==l[1][self.rules[n].r_e[k]] for k in [".".join((j,h,i)) for j in self.rules[n].i.graph for h in self.rules[n].i.graph[j] for i in self.rules[n].i.graph[j][h]]]) for l in t_r]):
                    return "The type graph language L(T) is not closed under the set of rules. Under Rule {}, there is no fitting t_R for t_L: {}".format(n,pprint_morphism(m))
                    
        return "The type graph language L(T) is closed under the set of rules. In every rule for every t_L there exists a fitting right-hand side counterpart t_R."

    def check_inv_gui(self):

        first_err = True

        yes_no = {n: (None, None) for n in self.rules}

        for n in self.rules:
            t_l = find_morphism(self.rules[n].l.graph, self.core_t.graph)
            t_r = find_morphism(self.rules[n].r.graph, self.core_t.graph)

            for m in t_l:
                if not any([all([m[0][self.rules[n].l_v[k]]==l[0][self.rules[n].r_v[k]]    for k in self.rules[n].i.graph]) and
                    all([m[1][self.rules[n].l_e[k]]==l[1][self.rules[n].r_e[k]] for k in [".".join((j,h,i)) for j in self.rules[n].i.graph for h in self.rules[n].i.graph[j] for i in self.rules[n].i.graph[j][h]]]) for l in t_r]):
                    yes_no[n] = (False, m)
                    if first_err:
                        first_err = False
                        if not messagebox.askyesno("", "A counterexample was found for one of the rules. Would you still like to check the other rules left?"):
                            return yes_no
                        else:
                            break

            if not yes_no[n][0] == False:
                yes_no[n] = (True, None)
                    
        return yes_no

class Inv_Chk_Gui:

    def __init__(self):

        self.top = Tk()

        self.top.title("inv_chk")

        self.menubar = Menu(self.top)
        self.filemenu = Menu(self.menubar, tearoff=0)
        self.filemenu.add_command(label="Open", command=self.open_file, accelerator="Ctrl-O")
        self.menubar.add_cascade(label="File", menu=self.filemenu)
        self.top.config(menu=self.menubar)

        self.frame_left = Frame(self.top)
        self.frame_left_top=Frame(master=self.frame_left)
        self.box_value = StringVar()
        self.box_value.set("Select which rule to show")
        self.rules_box = ttk.Combobox(master=self.frame_left_top, textvariable=self.box_value)
        self.check_button = Button(master=self.frame_left_top, text="chk_inv", command=lambda *_:self.check_inv())
        self.text = Text(master=self.frame_left, width=30, height=20, wrap=NONE, state=DISABLED)
        self.scroll_text = Scrollbar(master=self.frame_left, command=self.text.yview, orient=VERTICAL)

        self.frame_right = Frame(self.top, width=400, bg="white")
        self.canvas_l = Canvas(master=self.frame_right, bg="white")
        self.canvas_i = Canvas(master=self.frame_right, bg="white")
        self.canvas_r = Canvas(master=self.frame_right, bg="white")
        self.canvas_t = Canvas(master=self.frame_right, bg="white")

        self.label_l = Label(master=self.canvas_l, text="L")
        self.label_l.place(bordermode=INSIDE)
        self.label_i = Label(master=self.canvas_i, text="I")
        self.label_i.place(bordermode=INSIDE)
        self.label_r = Label(master=self.canvas_r, text="R")
        self.label_r.place(bordermode=INSIDE)
        self.label_t = Label(master=self.canvas_t, text="core(T)")
        self.label_t.place(bordermode=INSIDE)

        self.text.config(yscrollcommand=self.scroll_text.set)

        self.rules_box.pack(side=LEFT, fill=BOTH, expand=True)
        self.check_button.pack(side=RIGHT, fill=Y, expand=False)

        self.frame_left.columnconfigure(0, weight=1)
        self.frame_left.columnconfigure(1, weight=1)
        self.frame_left.rowconfigure(0, weight=0)
        self.frame_left.rowconfigure(1, weight=1)

        self.frame_left_top.grid(row=0,column=0, sticky="we")
        self.text.grid(row=1,column=0, sticky="nswe")
        self.scroll_text.grid(row=1,column=1, sticky="ns")
    
        self.frame_left.pack(side=LEFT, fill=Y, expand=False)


        self.canvas_l.grid(row=0, column=0,sticky="nswe")
        self.canvas_i.grid(row=0, column=1,sticky="nswe")
        self.canvas_r.grid(row=0, column=2,sticky="nswe")
        self.canvas_t.grid(row=1, column=0,columnspan=3,sticky="nswe")

        self.frame_right.columnconfigure(0, weight=1)
        self.frame_right.columnconfigure(1, weight=1)
        self.frame_right.columnconfigure(2, weight=1)
        self.frame_right.rowconfigure(0, weight=1)
        self.frame_right.rowconfigure(1, weight=3)
    
        self.frame_right.pack(side=RIGHT, fill=BOTH, expand=True)

        self.canvas_l.bind("<ButtonPress-1>", self.scroll_start)
        self.canvas_l.bind("<B1-Motion>", self.scroll_move)
        self.canvas_l.bind("<MouseWheel>",self.zoom)
        self.canvas_i.bind("<ButtonPress-1>", self.scroll_start)
        self.canvas_i.bind("<B1-Motion>", self.scroll_move)
        self.canvas_i.bind("<MouseWheel>",self.zoom)
        self.canvas_r.bind("<ButtonPress-1>", self.scroll_start)
        self.canvas_r.bind("<B1-Motion>", self.scroll_move)
        self.canvas_r.bind("<MouseWheel>",self.zoom)
        self.canvas_t.bind("<ButtonPress-1>", self.scroll_start)
        self.canvas_t.bind("<B1-Motion>", self.scroll_move)
        self.canvas_t.bind("<MouseWheel>",self.zoom)
        self.rules_box.bind("<<ComboboxSelected>>", lambda *_: self.render_r())

        self.canvases = {"l":self.canvas_l,"i":self.canvas_i,"r":self.canvas_r,"t":self.canvas_t}

        self.canvases_r = {self.canvases[n]:n for n in self.canvases}

        self.img = {n: None for n in self.canvases}
        self.pi = {n: None for n in self.canvases}

        self.inv_chk = None
        self.rule_map = None

        self.top.mainloop()

    def title(self):

        if not self.file:
            self.top.title("inv_chk")
        else:
            self.top.title(self.file+" - inv_chk")

    def open_file(self, *_):

        self.file = filedialog.askopenfilename(parent=self.top, initialdir=os.path.join(os.path.dirname(os.path.realpath(__file__)), "rules"), filetypes=[("Plain Text", ".txt"),("All Files", ".*")])

        if self.file:

            try:
                self.inv_chk = Inv_Chk(self.file)
            except Exception as e:
                return

            self.rules_box.config(values=[n for n in self.inv_chk.rules])

            f = open(self.file, "r")
            content = f.read()
            self.text.config(state=NORMAL)
            self.text.delete(1.0,END)
            self.text.insert(END, content)
            self.text.config(state=DISABLED)

            self.box_value.set("Select which rule to show")

            self.title()

            self.scale={n:1.0 for n in self.canvases}
            self.render_t()

    def render_t(self):

        if self.inv_chk:
            r = self.box_value.get().split(":")[0]
            if self.rule_map and r != "Select which rule to show" and self.rule_map[r][0] == False:
                g_color = self.rule_map[r][1]
                colors = color_scale(sum([len(set(g_color[0].values())),len(set(g_color[1].values()))]))

                match = {n:colors[i] for i,n in enumerate(list(set(g_color[0].values()))+list(set(g_color[1].values())))}

                l_v = {n: match[g_color[0][n]] for n in g_color[0]}
                l_e = {n: match[g_color[1][n]] for n in g_color[1]}

                t_v = {n: match[n] for n in g_color[0].values()}
                t_e = {n: match[n] for n in g_color[1].values()}

                self.img["t"] = Image.open(self.inv_chk.core_t.visualize(color=(t_v,t_e)))
                self.pi["t"] = ImageTk.PhotoImage(self.img["t"])
                self.scale["t"]=1.0
                self.re_render("t")

                self.img["l"] = Image.open(self.inv_chk.rules[r].l.visualize(color=(l_v,l_e)))
                self.pi["l"] = ImageTk.PhotoImage(self.img["l"])
                self.scale["l"]=1.0
                self.re_render("l")
            else:
                self.img["t"] = Image.open(self.inv_chk.core_t.visualize())

                self.pi["t"] = ImageTk.PhotoImage(self.img["t"])
                self.scale["t"]=1.0
                self.re_render("t")

    def render_r(self, *_):

        r = self.box_value.get()

        r = r.split(":")[0]

        if self.inv_chk:

            self.img["l"] = Image.open(self.inv_chk.rules[r].l.visualize())
            self.img["i"] = Image.open(self.inv_chk.rules[r].i.visualize())
            self.img["r"] = Image.open(self.inv_chk.rules[r].r.visualize())

            if self.rule_map:
                self.render_t()

            for n in self.canvases:
                if n != "t":
                    self.pi[n] = ImageTk.PhotoImage(self.img[n])
                    self.scale[n]=1.0
                    self.re_render(n)

    def re_render(self, canvas):

        img_cache = self.img[canvas].resize((int(self.img[canvas].size[0]*self.scale[canvas]),int(self.img[canvas].size[1]*self.scale[canvas])),Image.ANTIALIAS)
        self.pi[canvas] = ImageTk.PhotoImage(img_cache)
        self.canvases[canvas].delete("all")
        self.canvases[canvas].create_image(0, 0, anchor="nw", image=self.pi[canvas])
        self.canvases[canvas].config(scrollregion=self.canvases[canvas].bbox("all"))

    def check_inv(self, *_):

        if self.inv_chk:
            res = self.inv_chk.check_inv_gui()

            self.rule_map = res

            values = []

            for n in self.inv_chk.rules:
                if res[n][0] == True:
                    values.append(str(n)+": Invariant")
                elif res[n][0] == False:
                    values.append(str(n)+": Not Invariant")
                elif res[n][0] == None:
                    values.append(str(n)+": Unknown")

            self.rules_box.config(values=values)
            self.render_t()

    def scroll_start(self, event):
        event.widget.scan_mark(event.x, event.y)

    def scroll_move(self, event):
        event.widget.scan_dragto(event.x, event.y, gain=1)

    def zoom(self, e):

        c = self.canvases_r[e.widget]

        if (zoom_factor**-4)<=self.scale[c]*(zoom_factor**(e.delta/120))<=(zoom_factor**2):
            self.scale[c]*=(zoom_factor**(e.delta/120))
            self.re_render(c)

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

def color_scale(amount):

    pi = math.pi
    sin = math.sin
    floor = math.floor

    incr = (2*pi)/amount

    values = [[(sin((0)+n*incr)+1)/2, (sin(((2/3)*pi)+n*incr)+1)/2, (sin(((4/3)*pi)+n*incr)+1)/2] for n in range(amount)]

    values = [[floor(n[0]*256), floor(n[1]*256), floor(n[2]*256)] for n in values]

    values = [[hex(n[0])[2:], hex(n[1])[2:], hex(n[2])[2:]] for n in values]

    values = ["#"+"".join(n) for n in values]

    return values

if __name__ == '__main__':

    if len(sys.argv) > 1:
        assert type(sys.argv[1]) == str and os.path.isfile(sys.argv[1])
        print(Inv_Chk(sys.argv[1]).check_inv())
    else:
        Inv_Chk_Gui()