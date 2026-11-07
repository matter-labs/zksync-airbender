import sys,re
import os
P=os.path.dirname(os.path.abspath(__file__))+"/"
fam=sys.argv[1]
cols={}
for line in open(P+"struct.txt"):
    f=line.split(None,4)
    if f[0]!=fam: continue
    c=int(f[1]); s=int(f[2]); rest=f[3]+" "+f[4].strip()
    cols.setdefault(c,[]).append((s,rest))
for c in sorted(cols):
    items=[]
    for s,rest in cols[c]:
        k=rest.split()
        if k[0]=="G":
            g=rest.split(None,2)[2]
            g=re.sub(r"TABLE\[[^\]]*\]","iotaTable",g)
            items.append(f"({s}, .grid {k[1]} {g})")
        elif k[0]=="A" and int(k[1])>200:
            items.append(f"({s}, .affine {k[1]} {k[2]} {k[3]})")
    print(f"def col{c}Longs : List (Nat × Shape) :=\n  [" + ",\n    ".join(items)+"]\n")
