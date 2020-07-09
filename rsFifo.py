from z3 import *
class node
    index:int
    w:int
    dw:int
    def solve(self, parameter_list):
        s = Solver()
        head,tail=BitVecs('head tail',w)
        mem=Array('mem',BitVecSort(dw),BitVecSort(dw))
        if (index==0)
            sols=[]
        else:
            if (index%2==1)
                if (index==1)
                    s.add(tail==0)
                    s.add(emptyFifo==true)    
                else:
                    s.add(tail==(index/2 - 1))
                    s.add(emptyFifo==false)
        
        if 
        s.add(tail==head + 1)
        s.add(mem[head]==2)

        solvs=

        while s.check() == sat:
            print("model", n)
            n=n+1;
            m = s.model()
            for d in m:
                print(d, m[d])
            print(m.eval(mem[head]))
            s.add(Or(head != s.model()[head], tail != s.model()[tail]))


(let x=node2Nat n in
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
     )
