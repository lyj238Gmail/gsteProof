theory roundRobinArbiter imports paraGste1
begin

abbreviation rst::"varType" where
"rst \<equiv>  Ident ''rst''"

abbreviation req::"varType" where
"req\<equiv>  (Ident ''req'')"

abbreviation grant::"varType" where
"grant \<equiv>  (Ident ''grant'')"

abbreviation zero::"expType" where
"zero \<equiv> Const (index  0)"

abbreviation HIGH::"expType" where
" HIGH \<equiv> Const (boolV True)"


primrec roundFunc::"nat \<Rightarrow>nat\<Rightarrow>expType" where
"roundFunc k 0=Const (index k)"|
"roundFunc k (Suc bound) =
  iteForm (eqn (IVar (Para req k)) HIGH) (Const (index k)) (roundFunc ((k+1) mod (Suc bound)) bound)"



definition Statement::"nat \<Rightarrow> generalizeStatement" where 
"Statement bound\<equiv> 
  caseStatement 
     (map (\<lambda>i. (eqn (IVar grant) (Const (index i)), 
              Parallel [
              assign (grant,roundFunc i bound)])) ( upt 0 bound)) 
   "


abbreviation dataIn::"expType" where
"dataIn \<equiv> IVar (Ident ''dataIn'' )"




definition branches::"nat \<Rightarrow> generalizeStatement "

abbreviation emptyFifo::"expType" where
" emptyFifo \<equiv> IVar (Ident ''empty'' ) "

abbreviation tail::"expType" where
" tail \<equiv> IVar (Ident ''tail'' ) "

abbreviation head::"expType" where
" head \<equiv> IVar (Ident ''head'' ) "