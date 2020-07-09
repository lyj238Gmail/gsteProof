from z3 import *
class node
    def __init__(self, index,w, dw, d):
        self.w=w
        self.dw=dw
        self.d=d
        self.index=index

    def solve(self):
        s = Solver()
        head,tail=BitVecs('head tail',self.w)
        mem=Array('mem',BitVecSort(self.dw),BitVecSort(self.dw))
        if (self.index==0)
            sols=[]
        else:
            if (self.index%2==1)
                if (self.index==1)
                    s.add(tail==0)
                    s.add(emptyFifo==true)    
                else:
                    s.add(tail==(self.index/2 - 1))
                    s.add(emptyFifo==false)
            else:
                s.add(tail==(self.index/2 - 2))
                s.add(emptyFifo==false)
                s.add(mem[0]==d)

            sols=[]
            while s.check() == sat:
                print("model", n)
                m = s.model()
                sol=[]
                for d in m:
                    sol=sol.append(d,m[d])
                    print(d, m[d])
                print("mem",eval(mem[0]))
                sol=sol.append("mem",0)
                sols=sols.append(sol)
                s.add(Or( tail != s.model()[tail]))

w=node(15,4,64,0)
w.solve()
"""(let x=node2Nat n in
   let DataE=(Const (index DATA)) in
   if (x = 0) then [] else
    (if ((x mod 2) = 1) then 
      (if (x =1) then 
        [eqn tail (Const (index 0)), eqn  emptyFifo (Const (boolV True))]
       else [eqn tail (Const (index (x div 2 - 1 ))), eqn  emptyFifo (Const (boolV False))] )
    else 
    (if (x = 2) then [] else
     [eqn tail (Const (index (x div 2 - 2 ))), eqn  emptyFifo (Const (boolV False)), 
     eqn (IVar (Para (Ident ''mem'') 0)) DataE ]) )
     )"""
