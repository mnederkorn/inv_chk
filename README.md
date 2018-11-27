# inv_chk
Invariant Checking of type graph language based on core graph computation 

## Installation:

This tool is based on cores.py from: [CoReS](https://github.com/mnederkorn/CoReS)  
To run inv_chk you need to make cores.py available in your python context. E.g. by putting inv_chk.py in the same folder as cores.py.

## Usage:

To run inv_chk, pass it a filepath to a problem instance. E.g.:  
```python .\inv_chk.py "C:\Users\Maxime\Documents\GitHub\inv_chk\rules\bipartite_inv.txt"```

A problem instance is formated as follows:
```
T:
[type graph]
rules:
[list of rules]
```  
A rule is formated as follows:
```
I:
[interface graph]
L:
[left graph]
R:
[right graph]
morphL:
[morphism from the interface graph to left graph]
morphR:
[morphism from the interface graph to right graph]
```  
A graph is formated as follows:  
First line is a list of space separated integers which name the nodes of the graph.
All following lines consist of a single integer representing the source node of an edge, followed by a space and another integer representing the target node, followed by a space and a single capital letter denominating the lable of the given edge.  
A morphism is formated as follows:
```
V:
[list of node mappings]
E:
[list of edge mappings]
``` 
Mappings are formated as follow:
```  
[some node/edge in I]->[some node/edge in L/R]
``` 
Edge e is written as:
```src(e).tgt(e).lab(e)```

For example problem instances see:  
[bipartite_inv](rules/bipartite_inv.txt)  
[bipartite_not_inv](rules/bipartite_not_inv.txt)
