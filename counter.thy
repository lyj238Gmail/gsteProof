(* module countermem(clk,rst,counter,d,addr,q);
    parameter	    MSBD = 63;
    parameter	    DEPTH = 31;
    parameter	    MSBA = 4;
    input	    clk;
    input           rst;
    input [MSBD:0]  d;
    input [MSBA:0]  addr;
    input	    counter;
    output [MSBD:0] q;


    reg [MSBD:0]    mem[0:DEPTH];
    reg [MSBA:0]    write_addr;
     //wire [MSBA:0]  read_addr;
	integer i;

	initial begin
	for (i = 0; i <= DEPTH; i = i + 1)
	    mem[i] = 0;
 	write_addr = 0;
    end // initial begin


    always @ (posedge clk) begin
	if (rst) write_addr = 0;
	else if (counter) begin
		mem[write_addr] = d;
	    write_addr = write_addr +1;
	end 
    end // always @ (posedge clock)
	
    assign q = mem[write_addr-1-addr];

endmodule // *)
theory counter imports paraGste1
begin
abbreviation rst::"varType" where
"rst \<equiv>  (Ident ''rst'')"

abbreviation last::"varType" where
"last \<equiv>  (Ident ''last'')"



definition  vertexI::"node" where [simp]:
"vertexI \<equiv>Vertex  0"


definition  vertexL::"nat \<Rightarrow> node list" where [simp]:
"vertexL DEPTH  \<equiv>  (map (%i. Vertex  i) (upt 0 ( DEPTH +2)))"

lemma testUpto: "upt 0 2=[0,1]"
  by (simp add: upt_rec) 

definition edgeL::"nat \<Rightarrow> edge list" where [simp]:
 "edgeL DEPTH \<equiv>   (Edge (Vertex (DEPTH +1)) (Vertex 1))#
	  (map (%i.  ( Edge (Vertex ( i ))  (Vertex (  i + 1 ))) ) (upt 0  (DEPTH +1) )) "

lemma testUpto1:"upt 1 3=[Suc 0,2]" 
by (simp add: upt_rec) 

primrec node2Nat::"node \<Rightarrow> nat" where
"node2Nat (Vertex n) = n"

abbreviation LOW::"expType" where
"LOW \<equiv> Const (boolV False)"
abbreviation HIGH::"expType" where
"HIGH \<equiv> Const (boolV True)"

abbreviation rstForm::"formula" where
"rstForm  \<equiv>  (eqn (IVar rst) HIGH)" 

definition antOfCounterMem::"edge\<Rightarrow>formula" where [simp]:
"antOfCounterMem    edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
     if (	from = 0) then rstForm	else
      (neg rstForm))"



definition consOfCounterMem::" edge \<Rightarrow>formula" where  [simp]:
"consOfCounterMem     edge \<equiv>
(let from=node2Nat (source edge) in
 let to=node2Nat (sink edge) in
 if 	(from =0 ) then
  chaos
 else 
  eqn (IVar last) (Const (index (from - 1)))
 
  )"

definition counterGsteSpec::" nat\<Rightarrow>gsteSpec" where  [simp]:
"counterGsteSpec DEPTH\<equiv>Graph  vertexI (edgeL  DEPTH ) 
  (antOfCounterMem  )  (consOfCounterMem )"



definition tagFunOfCounterMem:: " nat\<Rightarrow>nodeTagFuncList" where [simp]:
"tagFunOfCounterMem  DEPTH  n \<equiv> 
  let x=node2Nat n in
   if (x = 0) then [] else
        [eqn (IVar last) (Const (index (x - 1)))]
 "
 
 abbreviation branch1::"generalizeStatement" where 
"branch1 \<equiv> 
  let S1=assign (last,(Const (index 0))) in
   Parallel [S1]"
   
abbreviation branch2::"nat\<Rightarrow>generalizeStatement" where 
"branch2 DEPTH \<equiv> 
  let S1= assign (last, 
    iteForm (eqn (IVar last) (Const (index DEPTH)))  (Const (index 0)) 
    (uif ''+'' [IVar last, (Const (index 1))])) in
   Parallel [S1]"   
   

abbreviation counterMem::" nat\<Rightarrow>generalizeStatement" where
"counterMem  DEPTH\<equiv> 
  caseStatement 
     [(eqn (IVar rst) HIGH, branch1),
      (neg (eqn (IVar rst) HIGH ), branch2 DEPTH)] 
   "
   

consts J::"  interpretFunType"  
  

axiomatization where axiomOnIAdd [simp,intro]:
" J ''+'' [index m, index (Suc 0)] = index ((m + 1))"  

lemma consistencyOfcounterMem:
  assumes a:"0 < DEPTH "
  shows "consistent' (counterMem DEPTH ) (J) (counterGsteSpec DEPTH ) 
  (tagFunOfCounterMem DEPTH)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (counterGsteSpec DEPTH )"
    let ?M="(counterMem DEPTH   )"
    let ?tag="(tagFunOfCounterMem   DEPTH)"
    let ?P ="\<lambda>e.   
    (let f=andListForm (?tag (sink e)) in
    let f'=andListForm (?tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  ( ?M))) (J))"
    
    assume a1:"e \<in> edgesOf (counterGsteSpec DEPTH )"
    
    have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex (DEPTH+1)) ( Vertex 1)  |
           (\<exists>i. 1\<le>i \<and> i\<le> DEPTH  \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) )    "
      apply(cut_tac a a1,auto)  done
    
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, simp  )
     done
     }
     moreover
    {assume b1:"e=Edge  ( Vertex (DEPTH+1)) ( Vertex 1)"
     have "?P e"
       apply(cut_tac a b1, simp )
       done
     
     } 
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> DEPTH  \<and>  e=( Edge (Vertex i)  (Vertex (  i + 1 ))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
     
      have "?P e"
        apply(cut_tac a b2 , auto  simp add:   Let_def)
        done
    }
    ultimately show "?P e" by satx
qed
    

lemma instImply:
assumes a:"G=(counterGsteSpec DEPTH)" and b:"0 < DEPTH "  and c:"tag=tagFunOfCounterMem  DEPTH"
shows
"\<forall> e. e \<in>edgesOf G\<longrightarrow> 
tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J)"  
proof(rule allI,rule impI,simp,rule allI,rule impI)
  fix e s
  assume a1:"e \<in> edgesOf G " and a2:"
           formEval (J) (antOf G e) s \<and> formEval (J) (andListForm (tag (source e))) s" 
  let ?P ="\<lambda>e. formEval (J) (consOf G e) s"           
  have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex (DEPTH+1)) ( Vertex 1)  |
           (\<exists>i. 1\<le>i \<and> i\<le> DEPTH  \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) ) "
         apply(cut_tac  a a1,auto)   done
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, auto) done
     }

    moreover
    {assume b1:"e=Edge ( Vertex (DEPTH+1)) ( Vertex 1)"
     have "?P e"
       apply(cut_tac a b c a1 a2 b1, auto) 
       done
     }

    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> DEPTH  \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) )   " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      
      have "?P e"
      proof(cut_tac a b c a2 b2, auto) qed
     
    }
      
    ultimately show "?P e" by satx
  qed      

lemma main: 
assumes a:"G=(counterGsteSpec DEPTH  )" and b:"0 < DEPTH " 
and c:"tag=tagFunOfCounterMem   DEPTH" and
d:"M=(counterMem DEPTH )"
shows " circuitSatGsteSpec M G (J)"  
proof(rule mainLemma)
have a1:"consistent' (counterMem DEPTH ) (J ) (counterGsteSpec DEPTH  ) (tagFunOfCounterMem   DEPTH)" 
   using b by (rule   consistencyOfcounterMem)
from a c d this show "consistent' M   (J) G tag"
  by simp   
next
from a b c show "\<forall>e. e \<in> edgesOf G \<longrightarrow>
        tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J)"
apply(rule instImply) done
next
from a c show "tag (initOf G) = []"
apply auto done
qed
end
