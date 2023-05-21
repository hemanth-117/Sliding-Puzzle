### TEAM MEMBERS
## MEMBER 1: 210050053
## MEMBER 2: 210050117
## MEMBER 3: 210050118


from z3 import *
import sys

file = sys.argv[1]

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])


num=T+1

X=[] # matrix
comp_c=[] # comparing two adajacent matrices condition

X.append(matrix) # initialising the matrix

# THESE FOUR ARRAYS STORE THE num DONE IN EACH STEP 

mix = []

mix.append([ Int("h_%s" % (i)) for i in range(num) ]) # variables for left/right/up/down

# removing the extra bracket
mix = mix[0]

# initialising the arrays
mix_c =[]
# Conditions on no,rc,lrud
mix_c=mix_c + ([ And(0 <= mix[i],mix[i] <= 4*n)
                for i in range(num) ])


cells_c = []
sq_c = []
comp_c = []

for k in range(1,num):
    X.append([ [ Int("x_%s_%s_%s" % (k,i+1, j+1)) for j in range(n) ]
        for i in range(n) ])
    if k>=1:
        for i in range(n):
            c1 = (mix[k] == i +1)
            x = True
            yl = [c1]
            for p in range(n):
                for q in range(n):
                    if(p==i):
                        o = X[k][p][q] == X[k-1][p][(q+1)%n]
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
            #comp_c += [Or(yl)]
            
        for i in range(n):
            c1 = (mix[k] == n+i+1 )
            x = True
            y = False
            for p in range(n):
                for q in range(n):
                    if(p==i):
                        o = X[k][p][q] == X[k-1][p][(q-1)%n]
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
            #comp_c += [Or(yl)]
        for i in range(n):
            c1 = (mix[k] == 2*n+i+1 )
            x = True
            y = False
            for p in range(n):
                for q in range(n):
                    if(q==i):
                        o = X[k][p][q] == X[k-1][(p+1)%n][q]
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
            #comp_c += [Or(yl)]

        for i in range(n):
            c1 = (mix[k] == 3*n+i+1)
            x = True
            y = False
            for p in range(n):
                for q in range(n):
                    if(q==i):
                        o = X[k][p][q] == X[k-1][(p-1)%n][q]
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))
                        
                    else:
                        o = (X[k][p][q] ==   X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))

        for i in range(n):
            c1 = (mix[k] == 0)
            x = True
            y = False
            for p in range(n):
                for q in range(n):
                        o = (X[k][p][q] ==   X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
                        yl.append(Not(o))             
       	   
comp_c+=[And(X[num-1][i][j]==n*i+j+1) for i in range(n) for j in range(n) ]
s = Solver()
s.add(comp_c+mix_c)
r = s.check()
print(r)

if r == sat:
    m = s.model()
    for k in range(1,num):
       
        r = [ [ m.evaluate(X[k][i][j]) for j in range(n) ]
            for i in range(n) ]

    g1 = [m.evaluate((mix[k]-1)%n).as_long() for k in range(num)]
    g2 = [m.evaluate(((mix[k]-1)/n)/2).as_long() for k in range(num)]
    g3 = [m.evaluate(((mix[k]-1)/n)%2).as_long() for k in range(num)]
    x=[['l','r'],
        ['u','d']]

    for k in range(1,num):
        if (g2[k]<0 or g1[k]<0):
            continue
        print(str(g1[k])+x[g2[k]][g3[k]])