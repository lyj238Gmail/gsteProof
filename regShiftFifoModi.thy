theory regShiftFifoModi imports paraGste1
begin
abbreviation rst::"expType" where
"rst \<equiv> IVar (Ident ''rst'')"

abbreviation push::"expType" where
"push \<equiv> IVar (Ident ''push'')"

abbreviation pop::"expType" where
"pop \<equiv> IVar (Ident ''pop'')"

abbreviation dataIn::"expType" where
"dataIn \<equiv> IVar (Ident ''dataIn'' )"



abbreviation LOW::"expType" where
"LOW \<equiv> Const (boolV False)"
abbreviation HIGH::"expType" where
" HIGH \<equiv> Const (boolV True)"

abbreviation emptyFifo::"expType" where
" emptyFifo \<equiv> IVar (Ident ''empty'' ) "

abbreviation tail::"expType" where
" tail \<equiv> IVar (Ident ''tail'' ) "

abbreviation head::"expType" where
" head \<equiv> IVar (Ident ''head'' ) "


abbreviation full::"expType" where
" full \<equiv> IVar (Ident ''full'' ) "

definition fullForm::"nat\<Rightarrow>formula" where [simp]:
" fullForm DEPTH\<equiv> eqn tail (Const (index DEPTH)) "

abbreviation mem::"nat \<Rightarrow> expType" where
"mem i \<equiv> IVar (Para (Ident ''mem'') i)"

type_synonym paraExpType="nat \<Rightarrow>expType"

 

abbreviation dataOut::"nat\<Rightarrow>expType" where
"dataOut DEPTH \<equiv> read (Ident ''mem'') DEPTH (IVar (Ident ''tail'' ))"


abbreviation rstForm::"formula" where
"rstForm  \<equiv>  (eqn rst HIGH)"

abbreviation emptyForm::"formula" where
"emptyForm  \<equiv>  (eqn emptyFifo HIGH)"
 
abbreviation pushForm::"formula" where
"pushForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push HIGH)) (eqn pop LOW)"

abbreviation popForm::"formula" where
"popForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop HIGH)"

abbreviation nPushPopForm::"formula" where
"nPushPopForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop LOW)"

abbreviation pushDataForm::"nat \<Rightarrow>formula" where
" pushDataForm D \<equiv>andForm pushForm  (eqn dataIn (Const (index D)))"

abbreviation popDataForm::"nat\<Rightarrow>nat \<Rightarrow>formula" where
" popDataForm DEPTH D \<equiv>  (eqn (dataOut DEPTH) (Const (index D)))"
 
abbreviation nFullForm::"nat \<Rightarrow>formula" where
"nFullForm  DEPTH\<equiv>  neg (fullForm DEPTH)"

abbreviation nEmptyForm::"formula" where
"nEmptyForm \<equiv> neg emptyForm "



definition  vertexI::"node" where [simp]:
"vertexI \<equiv>Vertex  0"

(*DEPTH=LAST + 1*)
definition  vertexL::"nat \<Rightarrow> node list" where [simp]:
"vertexL LAST  \<equiv>  vertexI # (map (%i. Vertex  i) (down LAST))"

definition edgeL::"nat \<Rightarrow> edge list" where [simp]:
 "edgeL LAST \<equiv> [Edge vertexI ( Vertex 1)]
    @ [Edge  ( Vertex 1) ( Vertex 3)]		
    @ [Edge  ( Vertex 1) ( Vertex 4)]	
    
		@(map (%i.  ( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) ) (upt 0  (LAST+2) ))  (* self-loop*)  
	  @(map (%i.  ( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) (upt 1  (LAST+2) ))  (* self-loop*)   
	  
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) ( upt 1 (LAST+1)))
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) ) ( upt 1 (LAST+1)))
		
		@(map (%i.   ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) (  upt 0 (LAST+1) )) 
		@(map (%i.   ( Edge (Vertex (2 * i + 4))  (Vertex (2 * i + 2))) ) (  upt 1 (LAST+1) ))
		@[Edge  ( Vertex 4) ( Vertex 1)]
	 "


primrec node2Nat::"node \<Rightarrow> nat" where
"node2Nat (Vertex n) = n"


definition antOfRbFifo::"nat\<Rightarrow>edge\<Rightarrow>formula" where [simp]:
"antOfRbFifo  D  edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
   if (from = 0) then rstForm	else
   if (from=to) then nPushPopForm else
      (if ((from mod 2) =1) then
        (
          if ((from + 2)=to) then ( pushForm ) else
          if (from=(to + 2)) then popForm else
          pushDataForm D )   
       else popForm))"



definition consOfRbFifo::"nat\<Rightarrow>nat\<Rightarrow>edge \<Rightarrow>formula" where  [simp]:
"consOfRbFifo   D LAST edge \<equiv>
(let from=node2Nat (source edge) in
 let to=node2Nat (sink edge) in
 if 	(((from mod 2) = 1) \<and> ((to mod 2) = 1)) then
    (if  from =1 then (andForm  emptyForm (nFullForm LAST))
     else if    (from = (2*LAST+3)) then (andForm nEmptyForm (fullForm LAST)) 
     else andForm nEmptyForm (nFullForm LAST))
 else if (from=4 \<and> to = 1) then popDataForm LAST D
 else if (from = (2*LAST+4)) then (andForm nEmptyForm (fullForm LAST)) 
 else if (from =1 )  then (andForm emptyForm (nFullForm LAST))
 else if (from \<noteq>0)   then (andForm nEmptyForm (nFullForm LAST))
 else chaos)"

definition rbFifoGsteSpec::" nat\<Rightarrow>nat\<Rightarrow>gsteSpec" where  [simp]:
"rbFifoGsteSpec LAST  data\<equiv>Graph  vertexI (edgeL  LAST ) (antOfRbFifo data )  (consOfRbFifo data  LAST)"

primrec applyPlusN::"expType\<Rightarrow>nat \<Rightarrow>expType" where
"applyPlusN e 0=e" |
"applyPlusN e (Suc N) = uif ''+'' [applyPlusN e N, Const (index 1)]"

definition tagFunOfRegShiftFifo:: " nat\<Rightarrow>nodeTagFuncList" where [simp]:
"tagFunOfRegShiftFifo DATA  n \<equiv> 
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
   
 "
 
 abbreviation branch1::"generalizeStatement" where 
"branch1 \<equiv> 
  (let S1=assign (Ident ''tail'',(Const (index 0))) in
   let S2=assign (Ident ''empty'',HIGH) in
   Parallel [S1,S2])"
   
abbreviation branch2::"nat\<Rightarrow>generalizeStatement" where 
"branch2 LAST \<equiv> 
  (let S1=map (\<lambda>i. assign ((Para (Ident ''mem'') i), 
    iteForm (eqn (Const (index i)) (Const (index 0))) dataIn 
    (read (Ident ''mem'')  LAST  (uif ''-'' [(Const (index i)), (Const (index 1))])))) (down LAST ) in
   let tailPlus=uif ''+'' [tail, (Const (index 1))] in
   let S2=assign (Ident ''tail'',iteForm (neg (eqn  emptyFifo HIGH)) tailPlus tail) in
   let S3=assign (Ident ''empty'',LOW) in
   Parallel ([S2,S3]@S1))"   
   
abbreviation branch3::"generalizeStatement" where 
"branch3 \<equiv> 
  (let S1=Parallel [assign (Ident ''empty'',HIGH)] in
   let S2=Parallel [ assign (Ident ''tail'', uif ''-'' [tail, (Const (index 1))])] in
    If (eqn tail (Const (index 0))) S1 S2)" 

definition tagFunOfRbfifio:: "nat \<Rightarrow> nat\<Rightarrow>nodeTagFuncList" where [simp]:
" tagFunOfRbfifio depth DATA  n \<equiv> 
  (let x=node2Nat n in
   let DataE=(Const (index DATA)) in
   if (x = 0) then [] else
    (if ((x mod 2) = 1) then 
      (if (x=1) then 
        [eqn tail (Const (index 0)), eqn  emptyFifo (Const (boolV True))]
       else [eqn tail (applyPlusN head (x div 2 )), eqn  emptyFifo (Const (boolV False))] )
   else 
   (if (x = (2)) then [] else
   [eqn tail (applyPlusN head ((x div 2) - 1)), eqn ( read (Ident ''mem'') depth tail) DataE ]) ))
 "
abbreviation shiftRegfifo::" nat\<Rightarrow>generalizeStatement" where
"shiftRegfifo  LAST\<equiv> 
  caseStatement 
     [(eqn rst HIGH, branch1),
      (andForm (eqn push HIGH) (neg (eqn tail (Const (index LAST)))), branch2 LAST),
      (andForm (eqn pop HIGH) (eqn emptyFifo LOW), branch3)] 
   "
  
consts J::" interpretFunType"  
  
axiomatization where axiomOnIAdd [simp,intro]:
"  J  ''+'' [index m, index (Suc 0)] = index (m + 1)" 

axiomatization where axiomOnISub [simp,intro ]: "  J  ''-'' [index m, index 1] = index (m - 1)"  


lemma consistencyOfRbfifo:
  assumes a:"0 < LAST "
  shows "consistent' (shiftRegfifo LAST ) (J ) (rbFifoGsteSpec LAST  data) (tagFunOfRegShiftFifo  data)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (rbFifoGsteSpec LAST  data)"
    let ?M="( shiftRegfifo  LAST )"
    let ?tag="(tagFunOfRegShiftFifo  data)"
    let ?P ="\<lambda>e.   
    (let f=andListForm (?tag (sink e)) in
    let f'=andListForm (?tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  ( ?M))) (J ))"
    assume a1:"e \<in> edgesOf (rbFifoGsteSpec LAST  data)"
    
    have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 3) |
          e=Edge  ( Vertex 1) ( Vertex 4)|
           (\<exists>i. 0\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> LAST +1\<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
            
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) )  |
           
           (\<exists>i. 0\<le>i \<and> i\<le> LAST  \<and>  e= ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST   \<and> e=( Edge (Vertex(2 * i + 4))  (Vertex(2 * i+2)))) |
            e=( Edge (Vertex 4) (Vertex 1))"
      apply(cut_tac a a1,auto)  done
    
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac b1, simp add:antOfRbFifo_def) done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }  
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 3) "
       have "?P e"
        apply(cut_tac a b1,auto ) done
    }
    
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 4) "
      let ?f="andForm (neg (eqn rst HIGH)) (andForm (eqn push HIGH) (neg (eqn tail (Const (index LAST )))) ) "
     
       have "?P e "
        apply(cut_tac a b1 ,auto) done
    }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i + 3))"     (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have b2:"i - 1 < LAST" by(cut_tac a b1,auto)
      have "?P e "
        apply(cut_tac  a b1 b2 ,auto simp add: antOfRbFifo_def assms ) done
     }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i+4))    "(is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have b2:"i - 1 < LAST" by(cut_tac a b1,auto)
      have "?P e "
        by(cut_tac a b1 b2 ,auto simp add: antOfRbFifo_def assms)
     } 
    
     moreover
    {assume b1:"\<exists>i. 0\<le>i \<and> i\<le> LAST \<and>  e=Edge  ( Vertex (2*i + 3)) ( Vertex (2*i + 1))   " (is "\<exists>i. ?Q i")
       from b1 obtain i where b1:"?Q i" by blast
       have "?P e "
       using  axiomOnISub  by(cut_tac  a b1 ,auto simp add: antOfRbFifo_def assms )
     }
    
     moreover
    {assume b1:"\<exists>i.  1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 4)) ( Vertex (2*i +2))   " (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
     
      have "?P e "
       using  axiomOnISub   apply(cut_tac  a b1  ,auto simp add: antOfRbFifo_def assms )
        done
     }
    moreover
    {assume b1:"e=Edge (Vertex 4) ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1,auto simp add:antOfRbFifo_def Let_def) done
     }
    ultimately show "?P e" by satx
  qed  

lemma testAux[simp]:
 
shows "(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem i)) (down LAST)@S))) s 
=expEval  I  (mem i) s) \<and>
(expEval I e s =index i \<longrightarrow>
 LAST < i\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem i)) (down LAST)@S))) s 
=expEval  I  (caseExp S) s)"  (is "?P LAST")
proof(induct_tac LAST,auto )qed 

lemma test[simp]:
shows "(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem i)) (down LAST)))) s 
=expEval  I  (mem i) s)"
proof -
have a:"(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), mem i)) (down LAST)@[]))) s 
=expEval  I  (mem i) s)"
apply(cut_tac testAux  [where S="[]"],blast)done
then show ?thesis by auto
qed

 

lemma instImply:
assumes a:"G=(rbFifoGsteSpec LAST  data)" and b:"0 < LAST "  and c:"tag=tagFunOfRegShiftFifo  data"
shows
"\<forall> e. e \<in>edgesOf G\<longrightarrow> 
tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) I"  
proof(rule allI,rule impI,simp,rule allI,rule impI)
  fix e s
  assume a1:"e \<in> edgesOf G " and a2:"
           formEval I (antOf G e) s \<and> formEval I (andListForm (tag (source e))) s" 
  let ?P ="\<lambda>e. formEval I (consOf G e) s"           
  have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 3) |
          e=Edge  ( Vertex 1) ( Vertex 4)|
           (\<exists>i. 0\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
            
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) )  |
           
           (\<exists>i. 0\<le>i \<and> i\<le> LAST  \<and>  e= ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST   \<and> e=( Edge (Vertex(2 * i + 4))  (Vertex(2 * i+2)))) |
            e=( Edge (Vertex 4) (Vertex 1))"
      apply(cut_tac a a1,auto)  done
     
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, auto simp add:antOfRbFifo_def)
 done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac a b c a2 b2, auto) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac  a b c a2 b2,auto) done
    }  
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 3) "
     
       have "?P e"
        apply(cut_tac a b c a2 b1,auto ) done
    }
    
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 4) "
       have "?P e "
        apply(cut_tac a b b1 c a2,auto simp add: antOfRbFifo_def ) done
    }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i + 3))"     (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
        by(cut_tac  a b c a2 b1 ,auto simp add: antOfRbFifo_def assms )
     }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i+4))    "(is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
        by(cut_tac  a b c a2 b1 ,auto simp add: antOfRbFifo_def assms)
     } 
    
     moreover
    {assume b1:"\<exists>i. 0\<le>i \<and> i\<le> LAST \<and>  e=Edge  ( Vertex (2*i + 3)) ( Vertex (2*i + 1))   " (is "\<exists>i. ?Q i")
       from b1 obtain i where b1:"?Q i" by blast
       have "?P e "
        by(cut_tac   a b c a2 b1 ,auto simp add: antOfRbFifo_def assms )
     }
    
     moreover
    {assume b1:"\<exists>i.  1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 4)) ( Vertex (2*i+2 ))   " (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
      by(cut_tac  a b c a2 b1 ,auto simp add: antOfRbFifo_def Let_def assms)
       
     }
    moreover
    {assume b1:"e=Edge (Vertex 4) ( Vertex 1)"
     have "?P e"
     apply(cut_tac  a b c a2 b1 ,auto) done
     }
    ultimately show "?P e" by satx
 qed      

lemma main: 
assumes a:"G=(rbFifoGsteSpec LAST  data)" and b:"0 < LAST " 
and c:"tag=tagFunOfRegShiftFifo  data" and
d:"M=(shiftRegfifo LAST )"
shows " circuitSatGsteSpec M G J "  
proof(rule mainLemma)
have a1:"consistent' (shiftRegfifo LAST ) (J ) (rbFifoGsteSpec LAST  data) (tagFunOfRegShiftFifo  data)" 
   using b by (rule   consistencyOfRbfifo)
from a c d this show "consistent' M   (J ) G tag"
  by simp   
next
from a b c show "\<forall>e. e \<in> edgesOf G \<longrightarrow>
        tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J )"
apply(rule instImply) done
next
from a c show "tag (initOf G) = []"
apply auto done
qed
end
