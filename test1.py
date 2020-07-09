from z3 import *
#head = Int('head')
#tail = Int('tail')
head,tail=BitVecs('head tail',2)
mem=Array('mem',BitVecSort(2),BitVecSort(2))

s = Solver()
s.add(tail==head + 1)
s.add(mem[head]==2)
#s.add(a <= 20)
#s.add(1 <= b)
#s.add(b <= 20)
#s.add(a >= 2*b)
n=0;

while s.check() == sat:
    print("model", n)
    n=n+1;
    m = s.model()
    for d in m:
        print(d, m[d])
#	print s.model()[mem]
    #num_entries = m[mem].num_entries()
    #for i in range(num_entries):
    #    print(m[mem].entry(i))
    #print("else", m[mem].else_value())
    print(m.eval(mem[head]))
    s.add(Or(head != s.model()[head], tail != s.model()[tail]))
