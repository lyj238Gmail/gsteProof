theory cube imports newparaGste1
begin

abbreviation c::"varType" where
"c \<equiv>  (Ident ''c'')"

abbreviation n::"varType" where
"n \<equiv>  (Ident ''n'')"

abbreviation k::"varType" where
"k \<equiv>  (Ident ''k'')"

abbreviation m::"varType" where
"m \<equiv>  (Ident ''m'')"



definition leRule::"nat \<Rightarrow> rule" where [simp]:
"leRule N\<equiv>
let g = uip ''<'' [IVar n, Const (index N)]  in
let s = parallel [(c, uif ''+'' [IVar c,IVar k]),
                  (k, uif ''+'' [IVar k,IVar m]),
                  (m, uif ''+'' [IVar m,Const (index 6)]),
                  (n, uif ''+'' [IVar n,Const (index 1)])]  in
guard g s"


consts J::" interpretFunType"  
  
axiomatization where axiomOnIAdd [simp,intro]:
"  J  ''+'' [index a,   index b] = index (a + b)"

axiomatization where axiomOnIMultiply [simp,intro]:
"  J  ''*'' [index a,   index b] = index (a * b)"

axiomatization where axiomOnLe [simp,intro]:  
"  J   ''leq'' [index a, index b]  = boolV (a \<le> b)" 

axiomatization where axiomOnLess [simp,intro]:  
"  J   ''<'' [index a, index b]  = boolV (a < b)" 

axiomatization where onVarn [simp,intro]:  
"  \<exists> a. s n= (index a)"


axiomatization where onVarc [simp,intro]:  
"  \<exists> a. s c= (index a)"

axiomatization where onVark [simp,intro]:  
"  \<exists> a. s k= (index a)"

axiomatization where onVarm [simp,intro]:  
"  \<exists> a. s m= (index a)"

subsection{*Definitions of initial states*}
definition initSpec0::" formula" where [simp]:
"initSpec0  \<equiv> 
andForm (eqn (IVar m) (Const (index 6)))
(andForm (eqn (IVar k) (Const (index 1)))
(andForm (eqn (IVar c) (Const (index 0)))
(eqn (IVar n) (Const (index 0)))))"

definition inv1::"formula" where [simp]:
"inv1 \<equiv>eqn ( IVar c) (uif ''*'' [(uif ''*'' [IVar n, IVar n]), IVar n])"

definition inv2::"formula" where [simp]:
"inv2\<equiv> eqn ( IVar k)
      (uif ''+'' 
      [(uif ''+'' [(uif ''*'' [(uif ''*'' [IVar n, IVar n]), Const (index 3)]),
                   (uif ''*'' [IVar n,  Const (index 3)])]),
      Const (index 1)])"

definition inv3::"formula" where [simp]:
"inv3 \<equiv> eqn (IVar m) (uif ''+'' [(uif ''*'' [IVar n,Const (index 6)]),Const (index 6)])"

definition inv4::"nat \<Rightarrow> formula" where [simp]:
"inv4 N \<equiv> uip ''leq'' [IVar n, Const (index N)]"

definition invariants::"nat \<Rightarrow>formula set" where [simp]:
"invariants N \<equiv> {inv1, inv2, inv3,inv4 N}"

lemma lemmaOnInv4:

shows "invHoldForRule' J s (inv4 N) (leRule N) (invariants N)"  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -

  have "\<exists> a. s n=(index a)"  by simp
    then obtain a where a1:"s n= index a" by blast
  from a1 have "?P1 s"
    by auto
  then show ?thesis by auto
qed
    
    
lemma lemmaOnInv3:

shows "invHoldForRule' J s (inv3 ) (leRule N) (invariants N)"   (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -

  have "\<exists> a. s n=(index a)"  by simp
  then obtain a where a1:"s n= index a" by blast

  have "\<exists> a. s m=(index a)"  by simp
  then obtain a' where a2:"s m= index a'" by blast

  from a1 a2 have "?P2 s"
    by auto

  then  show ?thesis  by auto
    
qed    

lemma lemmaOnInv2:

shows "invHoldForRule' J s (inv2 ) (leRule N) (invariants N)"   (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -

  have "\<exists> a. s n=(index a)"  by simp
  then obtain a where a1:"s n= index a" by blast

  have "\<exists> a. s k=(index a)"  by simp
  then obtain a' where a2:"s k= index a'" by blast

  from a1 a2   have "?P3 s  "
  proof(unfold invHoldForRule4_def,rule_tac x="{inv2,inv3}" in exI,auto )qed

  then show ?thesis by blast
    
qed    

lemma lemmaOnInv1:

shows "invHoldForRule' J s (inv1 ) (leRule N) (invariants N)"   (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -

  have "\<exists> a. s n=(index a)"  by simp
  then obtain a where a1:"s n= index a" by blast

  have "\<exists> a. s c=(index a)"  by simp
  then obtain a' where a2:"s c= index a'" by blast

  have "\<exists> a. s k=(index a)"  by simp
  then obtain a0 where a3:"s k= index a0" by blast

  have a4:"2 *(a*a) + a*a*a=(a+(a+a*a))*a"
    by (simp add: comm_semiring_class.distrib) 

  from a1 a2 a3 a4  have "?P3 s"  
  proof(unfold invHoldForRule4_def,rule_tac x="{inv1,inv2}" in exI,simp)qed
    
  then   show ?thesis  by blast
qed
    

lemma invs_on_rules:
  assumes a1: "f \<in> invariants N" and a2: "r \<in> {leRule N} "
  shows "invHoldForRule'  J s f r (invariants N)"
proof -

  have b1: "r=leRule N"
    apply (cut_tac a2, auto) done
  have "f=inv1 | f=inv2 |f=inv3 |f =inv4 N"
    using a1 by auto 
    moreover {
      assume c1: "f=inv1"
      have "invHoldForRule'  J s f r (invariants N )"
        using b1 c1 lemmaOnInv1 by blast
    }

  moreover {
      assume c1: "f=inv2"
      have "invHoldForRule'  J s f r (invariants N)"
        using b1 c1 lemmaOnInv2 by blast
    }
  moreover {
      assume c1: "f=inv3"
      have "invHoldForRule'  J s f r (invariants N)"
        using b1 c1 lemmaOnInv3 by blast
    }

  moreover {
      assume c1: "f=inv4 N"
      have "invHoldForRule'  J s f r (invariants N)"
        using b1 c1 lemmaOnInv4 by blast
    }
    ultimately show ?thesis by blast
qed 

lemma iniImply_inv:
assumes a1:"f \<in> invariants N" and a2: "formEval J (initSpec0) s"
shows "formEval J f s "
using a1 a2 by auto

lemma consistentCube: 
  shows " consistent'  J (invariants N) {initSpec0} {leRule N}"
proof(unfold  consistent'_def,rule conjI)
  show "\<forall>inv ini s. inv \<in> invariants N \<longrightarrow> ini \<in> {initSpec0} \<longrightarrow> formEval J ini s \<longrightarrow> formEval J inv s"
    using iniImply_inv by blast
next
  show "\<forall>inv r s. inv \<in> invariants N \<longrightarrow> r \<in> {leRule N} \<longrightarrow> invHoldForRule' J s inv r (invariants N)"
    
  by (smt consistent'_def iniImply_inv invs_on_rules singletonD)
qed

lemma cubeInv:
  assumes  a2:"s \<in> reachableSet J {initSpec0}  {leRule N}" 
  shows "\<forall> inv. inv \<in> invariants N\<longrightarrow>formEval J inv s"  (is "?P s")
  using assms consistentCube consistentLemma' by blast
  
end