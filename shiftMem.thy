(* module shiftmem(clk,rst,shift,d,addr,q);
    parameter	    MSBD = 63;
    parameter	    DEPTH = 31;
    parameter	    MSBA = 4;
    input	    clk;
    input           rst;
    input [MSBD:0]  d;
    input [MSBA:0]  addr;
    input	    shift;
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
	else if (shift) begin
		mem[write_addr] = d;
	    write_addr = write_addr +1;
	end 
    end // always @ (posedge clock)
	
    assign q = mem[write_addr-1-addr];

endmodule // *)
theory shiftMem imports paraGste1
begin
abbreviation rst::"expType" where
"rst \<equiv> IVar (Ident ''rst'')"

abbreviation shift::"expType" where
"shift \<equiv> IVar (Ident ''shift'')"

abbreviation adr::"expType" where
"adr \<equiv> IVar (Ident ''adr'')"

abbreviation wrt_adr::"expType" where
"wrt_adr \<equiv> IVar (Ident ''wrt_adr'')"

abbreviation dataIn::"expType" where
"dataIn \<equiv> IVar (Ident ''dataIn'' )"


abbreviation LOW::"expType" where
"LOW \<equiv> Const (boolV False)"
abbreviation HIGH::"expType" where
"HIGH \<equiv> Const (boolV True)"


abbreviation mem::"varType" where
"mem \<equiv>  Ident ''mem''" 

abbreviation q::"nat\<Rightarrow>expType" where
"q DEPTH \<equiv> read (Ident ''mem'') (DEPTH - 1) (uif  ''-'' [uif ''-'' [wrt_adr, (Const (index 1))],adr ])" 

abbreviation rstForm::"formula" where
"rstForm  \<equiv>  (eqn rst HIGH)" 
 
abbreviation shiftForm::"formula" where
"shiftForm \<equiv>  andForm (eqn rst LOW) (eqn shift HIGH)"

abbreviation readForm::"nat\<Rightarrow>formula" where
"readForm age\<equiv>   eqn adr (Const (index age))"

abbreviation initDataForm::"nat \<Rightarrow>formula" where
" initDataForm D \<equiv>andForm shiftForm  (eqn dataIn (Const (index D)))"

abbreviation retainRead::"formula" where
"retainRead \<equiv> andForm (eqn rst LOW) (eqn shift LOW)"

definition  vertexI::"node" where [simp]:
"vertexI \<equiv>Vertex  0"


definition  vertexL::"nat \<Rightarrow> node list" where [simp]:
"vertexL DEPTH  \<equiv>  vertexI # (map (%i. Vertex  i) (down DEPTH))"

definition edgeL::"nat \<Rightarrow> edge list" where [simp]:
 "edgeL DEPTH \<equiv> [Edge vertexI ( Vertex 1)]
   
    @ [Edge  ( Vertex 1) ( Vertex 2)]	
    
		@(map (%i.  ( Edge (Vertex ( i ))  (Vertex (  i+1 ))) ) (upt 2  (DEPTH +2) ))  (* self-loop*)  
	  @(map (%i.  ( Edge (Vertex ( i ))  (Vertex (  i ))) ) (upt 2  (DEPTH +2) ))  (* self-loop*)   
	 
	 "

lemma testUpto:"upt 1 3=[Suc 0,2]" apply auto
by (simp add: upt_rec) 

primrec node2Nat::"node \<Rightarrow> nat" where
"node2Nat (Vertex n) = n"


definition antOfShiftMem::"nat\<Rightarrow>edge\<Rightarrow>formula" where [simp]:
"antOfShiftMem   D  edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
     if (	from = 0) then rstForm	else
     if (from=1) then (initDataForm D) else
     if (from = to) then andForm retainRead (readForm (from - 2))
     else    andForm shiftForm (readForm (from -2)))"



definition consOfShiftMem::" nat\<Rightarrow>nat\<Rightarrow>edge \<Rightarrow>formula" where  [simp]:
"consOfShiftMem    D DEPTH edge \<equiv>
(let from=node2Nat (source edge) in
 let to=node2Nat (sink edge) in
 if 	(from =0 \<or> from=1) then
  chaos
 else 
  if (to \<le> DEPTH +1) then
  eqn (q DEPTH) (Const (index D))
  else chaos
  )"

definition shiftGsteSpec::" nat\<Rightarrow>nat\<Rightarrow>gsteSpec" where  [simp]:
"shiftGsteSpec DEPTH  data\<equiv>Graph  vertexI (edgeL  DEPTH ) 
  (antOfShiftMem data )  (consOfShiftMem data  DEPTH)"

primrec applyPlusN::"expType\<Rightarrow>nat \<Rightarrow>expType" where
"applyPlusN e 0=e" |
"applyPlusN e (Suc N) = uif ''+'' [applyPlusN e N, Const (index 1)]"

definition tagFunOfShiftMem:: " nat\<Rightarrow>nat\<Rightarrow>nodeTagFuncList" where [simp]:
"tagFunOfShiftMem DATA DEPTH  n \<equiv> 
  let x=node2Nat n in
   let DataE=(Const (index DATA)) in
   if (x = 0) then [] else
    if (x  = 1) then 
        [eqn wrt_adr (Const (index 0))]
    (*else if (x=2) then 
        [eqn wrt_adr (Const (index 1)), 
        eqn  (q 0) DataE
        ] *)
    else if (x \<le> DEPTH +1 ) then
        [eqn wrt_adr (Const (index ((x-1) ) )), eqn  (read mem (DEPTH - 1) (Const (index 0))) DataE]
    else []
 "
 
 abbreviation branch1::"generalizeStatement" where  (*  assume c1:"s (Ident ''adr'') = index (i - 2)" and
          c2:"s (Ident ''wrt_adr'') = index (i - Suc 0)" and
          c3:"s (Para mem 0) = index data"
        have b2:"expEval J (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) s=
        expEval J (Const (index 0)) s"
        apply(cut_tac b2 c1 c2,auto) done
        have b3:" expEval J
        (caseExp
        (map (\<lambda>i. (eqn (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) (Const (index i)), IVar (Para mem i))) (down DEPTH)))
        s =
        expEval J  (IVar (Para mem 0)) s"
        apply(cut_tac b2,auto) done
        show "expEval J
        (caseExp
          (map (\<lambda>i. (eqn (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) (Const (index i)), IVar (Para mem i)))
            (down DEPTH)))  s =
        index data "
       done*)
"branch1 \<equiv> 
  (let S1=assign (Ident ''wrt_adr'',(Const (index 0))) in
   Parallel [S1])"
   
abbreviation branch2::"nat\<Rightarrow>generalizeStatement" where 
"branch2 DEPTH \<equiv> 
  (let S1=map (\<lambda>i. assign ((Para (Ident ''mem'') i), 
    iteForm (eqn wrt_adr (Const (index i)))  dataIn 
    (IVar (Para (Ident ''mem'')  i)))) (down (DEPTH - 1) ) in
   let wrtAdrPlus=uif ''+'' [wrt_adr, (Const (index 1))] in
   let S2=assign (Ident ''wrt_adr'', wrtAdrPlus ) in
   Parallel (S2#S1))"   
   

abbreviation shiftMem::" nat\<Rightarrow>generalizeStatement" where
"shiftMem  DEPTH\<equiv> 
  caseStatement 
     [(eqn rst HIGH, branch1),
      (eqn shift HIGH , branch2 DEPTH)] 
   "
   

consts J::"nat \<Rightarrow>  interpretFunType"  
  

axiomatization where axiomOnIAdd [simp,intro]:
" J DEPTH ''+'' [index m, index (Suc 0)] = index ((m + 1))" 
(* (if m=DEPTH  then (index 0) else (index (m +1 )))"
index ((m + 1) mod (Suc DEPTH  )) " *)

axiomatization where axiomOnISub [simp,intro ]: "  J DEPTH  ''-'' [index m, index n] = index (m - n)"
(*axiomatization where axiomOnLe [simp,intro]:  
"  J DEPTH  ''le'' [index m, index n]  = boolV (m \<le> n)" *)
(*  axiomatization where axiomOn_procCmd  [simp]:"   s (IVar (Para ''procCmd'' i )) \<in> NODE_CMDType "*)

(*lemma test4:"m - 1< DEPTH \<and> 1 \<le> m \<Longrightarrow>I DEPTH ''+'' [index( m - 1 ), index 1] = index ((m   ) )" 
apply auto done*)
(*lemma aux1:"J DEPTH ''+'' [index m, index (Suc 0)] \<noteq> index m"

using axiomOnIAdd by simp*)
(*lemma aux2:"
substExp (caseExp (map (\<lambda>i. (f i, IVar (Para mem i))) (down DEPTH)))
            ((Ident v, e) #AS) =
substExp (caseExp (map (\<lambda>i. (f i, IVar (Para mem i))) (down DEPTH)))
            AS           "
proof(induct_tac DEPTH, auto   )   
lemma existI:
assumes a1:"formEval  J (uip ''le'' [head,LASTE]) s"
shows "\<exists>i. ((s (Ident ''head'') ) = (index i))" (*  assume c1:"s (Ident ''adr'') = index (i - 2)" and
          c2:"s (Ident ''wrt_adr'') = index (i - Suc 0)" and
          c3:"s (Para mem 0) = index data"
        have b2:"expEval J (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) s=
        expEval J (Const (index 0)) s"
        apply(cut_tac b2 c1 c2,auto) done
        have b3:" expEval J
        (caseExp
        (map (\<lambda>i. (eqn (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) (Const (index i)), IVar (Para mem i))) (down DEPTH)))
        s =
        expEval J  (IVar (Para mem 0)) s"
        apply(cut_tac b2,auto) done
        show "expEval J
        (caseExp
          (map (\<lambda>i. (eqn (uif ''-'' [uif ''-'' [wrt_adr, Const (index (Suc 0))], adr]) (Const (index i)), IVar (Para mem i)))
            (down DEPTH)))  s =
        index data "
       done*)
proof(cut_tac a1,case_tac "s (Ident ''head'')",auto)
qed*) 



lemma auxOnReadWrite[simp]:
"expEval I e s=expEval I e' s \<and>expEval I e s=index i\<and> i\<le> DEPTH \<longrightarrow>(\<forall>j. Para mem j \<notin>set (varOfExp e'))\<longrightarrow> 

        expEval I  (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down DEPTH)))
            (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i))))
              (down DEPTH)))
          s = expEval I e'' s "   (is "?P DEPTH")
proof(induct_tac DEPTH) 
  show "?P 0"
  proof(rule impI)+
  assume a1:" expEval I e s = expEval I e' s \<and> expEval I e s = index i \<and> i \<le> 0" and 
   a2:" \<forall>j. Para mem j \<notin> set (varOfExp e')"
   have a3:"(Para mem 0) \<notin> set (varOfExp e')"
    by(cut_tac a2,auto)
  show " expEval I
     (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down 0)))
       (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i)))) (down 0)))
     s = 
    expEval I e'' s"
   using a1 a3 noEffectSubstExp proof(cut_tac a1,auto)qed
   qed
  next
  fix n
  assume a0:  "?P n"
  show "?P (Suc n)"
  proof(rule impI)+
  assume a1:" expEval I e s = expEval I e' s \<and> expEval I e s = index i \<and> i \<le> Suc n" and 
   a2:" \<forall>j. Para mem j \<notin> set (varOfExp e')"
   have a3:"(Para mem  (Suc n)) \<notin> set (varOfExp e')"
    by(cut_tac a2,auto) 
   show "expEval I
     (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down (Suc n))))
       (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i)))) (down (Suc n))))
     s =
    expEval I e'' s" (is "?LHS (Suc n) =?RHS")
   proof(case_tac "i \<le> n")
     assume b1:"i \<le> n"
     have b2:" (Para mem (Suc n)) \<notin> set (varOfExp
     (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down n))))" 
      apply(auto)
      apply (simp add: SucnIsNotInDownn)
      by (simp add: a3)
      
     have b3:"?LHS (Suc n) =?LHS n" 
     using a1 a2 a3 b1 b2 by auto
     have b4:"?LHS n =   expEval I e'' s"
     using a1 b1 a2 a0 apply auto  done
     show "?LHS (Suc n) =?RHS"
     using b4 b3 by auto
   next
    assume b1:"\<not>i \<le> n"
    have b2:"i=Suc n" 
    using b1 a1 by auto
    show "?LHS (Suc n) =?RHS"
     using b1 b2 a1 a2 a3  apply auto done
  qed
qed  
qed

lemma aux1[simp]:"expEval (J DEPTH0) (caseExp (map (\<lambda>i. (eqn (Const (index 0)) (Const (index i)), IVar (Para mem i))) (down DEPTH))) s =
 expEval (J DEPTH0) (IVar ( Para mem 0)) s"
proof(induct_tac DEPTH,auto)
qed

lemma aux2[simp]:
  
  shows "
         expEval (J DEPTH0)
          (substExp (caseExp (map (\<lambda>i. (eqn (Const (index 0)) (Const (index i)), IVar (Para mem i))) (down DEPTH)))
            subst)
          s =expEval (J DEPTH0) (substExp (IVar (Para mem 0)) 
          subst) s "
  (is "?P DEPTH")
proof(induct_tac DEPTH)
  show "?P 0"  apply( auto) done
  next
  fix n
  assume b0:"?P n"
  have b1:"expEval (J DEPTH0)
          (substExp (caseExp (map (\<lambda>i. (eqn (Const (index 0)) (Const (index i)), IVar (Para mem i))) (down (Suc n))))
            subst)
          s=expEval (J DEPTH0)
          (substExp (caseExp (map (\<lambda>i. (eqn (Const (index 0)) (Const (index i)), IVar (Para mem i))) (down ( n))))
            subst)
          s"
          apply auto done


  show "?P (Suc n)" by(cut_tac b0 b1,auto) 
qed

lemma onMem0[simp]:
  shows "
          (substExp (IVar (Para mem 0)) 
            (map (\<lambda>i. (Para mem i, iteForm (eqn wrt_adr (Const (index i))) dataIn (IVar (Para mem i)))) (down DEPTH)))  =
        iteForm (eqn wrt_adr (Const (index 0))) dataIn (IVar (Para mem 0))"
proof(induct_tac DEPTH,auto)    qed   
   
lemma caseExpCong:
  assumes a:"tautlogy (eqn e e') I"
  shows "expEval I   (caseExp (map (\<lambda>i. (eqn e (Const (index i)), IVar (Para mem i))) (down DEPTH))) s
  =expEval I  (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down DEPTH))) s"
proof(induct_tac DEPTH,(cut_tac a,simp)+)qed

lemma caseExpCong1:
  assumes a:"formEval I (eqn e e') s "
  shows "expEval I   (caseExp (map (\<lambda>i. (eqn e (Const (index i)), IVar (Para mem i))) (down DEPTH))) s
  =expEval I  (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down DEPTH))) s"
proof(induct_tac DEPTH,(cut_tac a,simp)+)qed

lemma readWrite[simp,intro!]:
assumes a1:"expEval I e s=expEval I e' s " and a2:"expEval I e s=index i" and a3:" i\<le> DEPTH " and
a2:"(\<forall>j. Para mem j \<notin>set (varOfExp e'))" 

shows " expEval I  (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down DEPTH)))
            (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i))))
              (down DEPTH)))
          s = expEval I e'' s "
using a2 a3 assms(2) auxOnReadWrite local.a1 by blast

(*lemma onApplyPlusI[simp]:"
  0 <  DEPTH \<longrightarrow> J DEPTH ''+'' [index i, index (Suc 0)]  = index ((i + 1) mod DEPTH)  "
  proof(induct_tac i,auto) 
qed*)

lemma consistencyOfshiftMem:
  assumes a:"0 < DEPTH "
  shows "consistent' (shiftMem DEPTH ) (J DEPTH) (shiftGsteSpec DEPTH  data) 
  (tagFunOfShiftMem  data DEPTH)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (shiftGsteSpec DEPTH  data)"
    let ?M="(shiftMem DEPTH   )"
    let ?tag="(tagFunOfShiftMem  data DEPTH)"
    let ?P ="\<lambda>e.   
    (let f=andListForm (?tag (sink e)) in
    let f'=andListForm (?tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  ( ?M))) (J DEPTH))"
    
    assume a1:"e \<in> edgesOf (shiftGsteSpec DEPTH  data)"
    
    have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 2)  |
           (\<exists>i. 2\<le>i \<and> i\<le> DEPTH + 1 \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) )   |
            (\<exists>i. 2\<le>i \<and> i\<le> DEPTH +1  \<and>  e=( Edge (Vertex i)  (Vertex i)) ) "
      apply(cut_tac a a1,auto)  done
    
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, simp  )
     done
     }
     moreover
    {assume b1:"e=Edge (Vertex 1) (Vertex 2)"
     have "?P e"
     apply(cut_tac a b1, auto  )done
     (*by (metis One_nat_def Suc_eq_plus1 axiomOnIAdd)*) 
     
     } 
    moreover
    {assume b1:" (\<exists>i. 2\<le>i \<and> i\<le> DEPTH+1  \<and>  e=( Edge (Vertex i)  (Vertex (  i + 1 ))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
     have b3:"Ident ''wrt_adr'' \<notin> set
     (varOfExp  (caseExp (map (\<lambda>i. (eqn (Const (index 0)) (Const (index i)), IVar (Para mem i))) (down DEPTH))))"
      by(induct_tac DEPTH,auto)
      have "?P e"
       apply(cut_tac a b2 b3,  simp add:   Let_def)done
    }
    moreover
    {assume b1:" (\<exists>i. 2\<le>i \<and> i\<le> DEPTH +1 \<and>  e=( Edge (Vertex (i))  (Vertex (i))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, auto simp add: substNIl) done
    }  
    ultimately show "?P e" by satx
qed
    
lemma testAux[simp]:
 
shows "(expEval I e s =index i \<longrightarrow>
i \<le> DEPTH\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)),  mem0 i)) (down DEPTH)@S))) s 
=expEval  I  ( mem0 i) s) \<and>
(expEval I e s =index i \<longrightarrow>
 DEPTH < i\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)),   mem0 i)) (down DEPTH)@S))) s 
=expEval  I  (caseExp S) s)"  (is "?P DEPTH")
proof(induct_tac DEPTH,auto )qed 

lemma test[simp]:
shows "(expEval I e s =index i \<longrightarrow>
i \<le> DEPTH\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem0 i)) (down DEPTH)))) s 
=expEval  I  (mem0 i) s)"
proof -
have a:"(expEval I e s =index i \<longrightarrow>
i \<le> DEPTH\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem0 i)) (down DEPTH)@[]))) s 
=expEval  I  (mem0 i) s) \<and>
(expEval I e s =index i \<longrightarrow>
 DEPTH < i\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)),   mem0 i)) (down DEPTH)@[]))) s 
=expEval  I  (caseExp []) s)"
apply(rule_tac testAux  [where S="[]"])done
then show ?thesis by auto
qed

 

lemma instImply:
assumes a:"G=(shiftGsteSpec DEPTH  data)" and b:"0 < DEPTH "  and c:"tag=tagFunOfShiftMem  data DEPTH"
shows
"\<forall> e. e \<in>edgesOf G\<longrightarrow> 
tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J DEPTH)"  
proof(rule allI,rule impI,simp,rule allI,rule impI)
  fix e s
  assume a1:"e \<in> edgesOf G " and a2:"
           formEval (J DEPTH) (antOf G e) s \<and> formEval (J DEPTH) (andListForm (tag (source e))) s" 
  let ?P ="\<lambda>e. formEval (J DEPTH) (consOf G e) s"           
  have "e=Edge vertexI ( Vertex 1) | 
        e=Edge  ( Vertex 1) ( Vertex 2)  |
        (\<exists>i. 2\<le>i \<and> i\<le> DEPTH + 1 \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) )   |
        (\<exists>i. 2\<le>i \<and> i\<le> DEPTH + 1 \<and>  e=( Edge (Vertex i)  (Vertex i)) ) "
         apply(cut_tac  a a1,auto)   done
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, auto) done
     }

    moreover
    {assume b1:"e=Edge ( Vertex 1) ( Vertex 2)"
     have "?P e"
     apply(cut_tac a b1, auto) done
     }

    moreover
    {assume b1:" (\<exists>i. 2\<le>i \<and> i\<le> DEPTH + 1 \<and>  e=( Edge (Vertex i)  (Vertex (  i+1 ))) )   " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      
      have "?P e"
      proof(cut_tac a b c a2 b2, auto) qed
     
    }
    moreover
    {assume b1:"  (\<exists>i. 2\<le>i \<and> i\<le> DEPTH+1  \<and>  e=( Edge (Vertex i)  (Vertex (  i ))))   " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac  a b c a2 b2,auto) done
    }  
      
    ultimately show "?P e" by satx
  qed      

lemma main: 
assumes a:"G=(shiftGsteSpec DEPTH  data)" and b:"0 < DEPTH " 
and c:"tag=tagFunOfShiftMem  data DEPTH" and
d:"M=(shiftMem DEPTH )"
shows " circuitSatGsteSpec M G (J DEPTH)"  
proof(rule mainLemma)
have a1:"consistent' (shiftMem DEPTH ) (J DEPTH) (shiftGsteSpec DEPTH  data) (tagFunOfShiftMem  data DEPTH)" 
   using b by (rule   consistencyOfshiftMem)
from a c d this show "consistent' M   (J DEPTH) G tag"
  by simp   
next
from a b c show "\<forall>e. e \<in> edgesOf G \<longrightarrow>
        tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J DEPTH)"
apply(rule instImply) done
next
from a c show "tag (initOf G) = []"
apply auto done
qed
end
