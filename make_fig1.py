import random
K=12; seed=113; extra=6
rnd=random.Random(seed); H=[0]*K; first={}; parts=[]; n=0
while True:
    j=rnd.randrange(K); n+=1; h=1+max(H[(j-1)%K],H[j],H[(j+1)%K]); H[j]=h; parts.append((j,h,n)); first.setdefault(j,n)
    if len(first)==K: break
for _ in range(extra):
    j=rnd.randrange(K); n+=1; h=1+max(H[(j-1)%K],H[j],H[(j+1)%K]); H[j]=h; parts.append((j,h,n))
t=[first[x] for x in range(K)]
roots=[x for x in range(K) if t[x]<t[(x-1)%K] and t[x]<t[(x+1)%K]]
assert roots==[0,4,7,10] and {j for j,h,_ in parts if h==1}==set(roots)
xu=0.85; yu=0.42; ty=0.21; off=-4.75   # x unit, particle height, first-arrival scale, panel (b) baseline
L=[]
A=L.append
A(r"\documentclass[border=2pt]{standalone}")
A(r"\usepackage{tikz}\usetikzlibrary{decorations.pathreplacing}")
A(r"\begin{document}\begin{tikzpicture}[font=\small]")
# panel (a): deposited particles
A(r"\node[anchor=west] at (-0.2,%.2f) {(a) Deposition after %d steps};" % (max(H)*yu+0.45, n))
A(r"\draw[thin] (0,0) -- (%.2f,0);" % (K*xu))
for (j,h,s) in parts:
    x0=j*xu; y0=(h-1)*yu
    if h==1:
        A(r"\filldraw[fill=black,draw=black,line width=0.3pt] (%.3f,%.3f) rectangle (%.3f,%.3f);" % (x0+0.03,y0+0.02,x0+xu-0.03,y0+yu-0.02))
    else:
        A(r"\filldraw[fill=black!18,draw=black!55,line width=0.3pt] (%.3f,%.3f) rectangle (%.3f,%.3f);" % (x0+0.03,y0+0.02,x0+xu-0.03,y0+yu-0.02))
for x in range(K):
    A(r"\node[font=\scriptsize] at (%.3f,-0.25) {%d};" % (x*xu+xu/2, x))
A(r"\node[font=\scriptsize,anchor=east] at (-0.05,-0.25) {site};")
# panel (b): first-arrival landscape
top=off+16*ty
A(r"\node[anchor=west] at (-0.2,%.2f) {(b) Step of first visit};" % (top+0.35))
A(r"\draw[thin] (0,%.2f) -- (%.2f,%.2f);" % (off, (K+1)*xu, off))
for v in (5,10,15):
    A(r"\draw[black!25,very thin] (0,%.3f) -- (%.3f,%.3f); \node[font=\scriptsize,anchor=east] at (0,%.3f) {%d};" % (off+v*ty,(K+1)*xu,off+v*ty,off+v*ty,v))
pts=[(x*xu+xu/2, off+t[x]*ty) for x in range(K)]
wrap=(K*xu+xu/2, off+t[0]*ty)
A(r"\draw[line width=0.6pt] " + " -- ".join("(%.3f,%.3f)"%p for p in pts) + ";")
A(r"\draw[line width=0.6pt,dashed] (%.3f,%.3f) -- (%.3f,%.3f);" % (pts[-1]+wrap))
for x,(px,py) in enumerate(pts):
    if x in roots:
        A(r"\fill (%.3f,%.3f) circle (2.3pt);" % (px,py))
    else:
        A(r"\filldraw[fill=white,draw=black,line width=0.5pt] (%.3f,%.3f) circle (2pt);" % (px,py))
A(r"\fill[black!45] (%.3f,%.3f) circle (2.3pt);" % wrap)
A(r"\node[font=\scriptsize,black!60,anchor=west] at (%.3f,%.3f) {site 0 again};" % (wrap[0]+0.1, wrap[1]))
# gap braces under panel (b)
rr=roots+[K]
for k in range(len(roots)):
    a=rr[k]*xu+xu/2; b=rr[k+1]*xu+xu/2; g=rr[k+1]-rr[k]
    A(r"\draw[decorate,decoration={brace,mirror,amplitude=3pt}] (%.3f,%.3f) -- (%.3f,%.3f) node[midway,below=3pt,font=\scriptsize] {gap %d};" % (a+0.06,off-0.12,b-0.06,off-0.12,g))
# run labels for the first gap 0 -> 4 (t = 1, 12, 14, 9, 4)
A(r"\node[font=\scriptsize,anchor=east] at (%.3f,%.3f) {up};" % (pts[1][0]-0.05, (pts[0][1]+pts[2][1])/2+0.35))
A(r"\node[font=\scriptsize,anchor=west] at (%.3f,%.3f) {down};" % (pts[3][0]+0.12, (pts[2][1]+pts[4][1])/2+0.3))
A(r"\end{tikzpicture}\end{document}")
open('fig_reduction.tex','w').write("\n".join(L))
print('t =',t,'roots =',roots,'n =',n,'maxH =',max(H))
