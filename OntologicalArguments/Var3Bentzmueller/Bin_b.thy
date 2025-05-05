theory Bin_b
imports Main "../QML_var"

begin

(*Note sigma sends individuals to bool typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals" *)

section \<open>* Modified Bentzmuller Simplified Ontological Argument -- varying domain (individuals) *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"          
  
consts H :: "\<mu> \<Rightarrow> \<sigma>"
consts U1 :: "\<mu> \<Rightarrow> \<sigma>" (*Horn property- true for narwals *)
consts U2 :: "\<mu> \<Rightarrow> \<sigma>" (*Horse property*)
consts U3 :: "\<mu> \<Rightarrow> \<sigma>" (*Lives in Switzerland*)

axiomatization where
    M1:  "\<exists>x y.  x r x \<and> x\<noteq>y" and (*More than one world *)
    M2:  "\<exists>w. (w r w) \<and> ((\<^bold>\<exists>\<^sup>Ex. (\<^bold>\<exists>\<^sup>Ey. (\<^bold>\<not>(x \<^bold>=\<^sup>L y))) ) w)"   (*world with more than one individual *)
    
definition G3 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G3 x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( ( (\<Phi> x ))) )"


definition D :: "\<mu> \<Rightarrow> \<sigma>" where
  " D (x) \<equiv> \<^bold>\<not>(G3(x))"
  
definition DL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DL (x) \<equiv> \<^bold>\<not>(D(x))"  
    
definition Perfective1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective1 (\<phi>)  \<equiv> ( (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))"  
    
definition Perfective2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"      
  
definition Perfective ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"
    
definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
      
definition G0 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G0 x \<equiv> \<^bold>\<forall>\<Phi>.( P(\<Phi>) \<^bold>\<rightarrow>  ( ((\<Phi> x ))) )"                   
            
definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective1 \<Phi> \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"      
    
definition G1P :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1P x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )" 

definition GP :: "\<mu> \<Rightarrow> \<sigma>" where 
            "GP x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
(*Basic Results *)    
  
    
(*Note that the Isar proof works for when D is simply a consts*)    
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  apply (metis DL_def D_def Perfective1_def)
  prf
  done


subsection \<open>* Consistency *\<close>

  lemma True 
    nitpick [satisfy, user_axioms, expect = genuine] oops
      
subsection \<open>* HOL *\<close>

(*Proof found,/nitpick failed *)    
theorem Taut: " L \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
subsection \<open>* Anderson *\<close>   

axiomatization where
refl: "\<forall>w. (w r w)"

lemma helper1 : "\<lfloor> \<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>.  (Perfective1(\<Phi>)  \<^bold>\<and> (\<^bold>\<forall>\<^sup>Ex. (\<Phi>(x)  \<^bold>\<rightarrow>  \<Psi>(x)))   \<^bold>\<rightarrow>  (\<^bold>\<forall>\<^sup>Ex. ( \<^bold>\<not> (\<Psi>(x))  \<^bold>\<rightarrow>  \<^bold>\<not> (\<Phi>(x)) )) )\<rfloor>"
  by auto

lemma helper2 : "\<lfloor> \<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>.  (Perfective1(\<Phi>)  \<^bold>\<and> (\<^bold>\<forall>\<^sup>Ex. (\<Phi>(x)  \<^bold>\<rightarrow>  \<Psi>(x)))   \<^bold>\<rightarrow>  (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<Phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))\<rfloor>"
  using Perfective1_def by auto

lemma Bentz2 : "\<lfloor> \<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>.  (Perfective1(\<Phi>)  \<^bold>\<and> (\<^bold>\<forall>\<^sup>Ex. (\<Phi>(x)  \<^bold>\<rightarrow>  \<Psi>(x)))   \<^bold>\<rightarrow>   Perfective1(\<Psi>))\<rfloor>"   
  using helper1 helper2 Perfective1_def by metis


(*For BentzPrelim *)
lemma helper3:  "\<lfloor> Perfective1(G3) \<rfloor>"  
  using Giv Perfective1_def D_def by metis

lemma helper4:  "\<lfloor> Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx))   \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex. (x \<^bold>=\<^sup>Lx)  \<^bold>\<rightarrow> D(x) )  \<rfloor>" 
  using refl Perfective1_def by metis

lemma helper5:  "\<lfloor> Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx))   \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex. D(x) )  \<rfloor>" 
  using refl Perfective1_def by metis

lemma BentzPrelim : "\<lfloor>   \<^bold>\<diamond>  ( \<^bold>\<not> (Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx)))) \<rfloor> "
  nitpick[user_axioms] oops

lemma Bentz3 :  "\<lfloor> Perfective1(G0) \<rfloor>"  
  using G0_def G3_def Bentz2 helper3 by metis

axiomatization where
pss: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G3 x)\<rfloor>"

(*Proof found for G3, G0 is CS *)
lemma BentzPrelimAttempt2 : "\<lfloor>   \<^bold>\<diamond>  ( \<^bold>\<not> (Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx)))) \<rfloor> "
  using Giv helper5 Perfective1_def refl pss by metis

consts B :: " (\<mu> \<Rightarrow> \<sigma>)"

definition BarcB  ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
     "BarcB (\<Phi>)  \<equiv> (( \<^bold>\<not> (Perfective1( \<Phi>))  \<^bold>\<and>  (\<^bold>\<forall>\<^sup>Ex. ( \<Phi>(x)  \<^bold>\<leftrightarrow> ( \<lambda>y.  \<^bold>\<not>(y \<^bold>=\<^sup>Ly))(x) ))   ))"


lemma dawg:  "\<lfloor>  \<^bold>\<box> ( \<^bold>\<exists> \<Phi>. (( \<^bold>\<not> (Perfective1( \<Phi>))  \<^bold>\<and>  (\<^bold>\<forall>\<^sup>Ex. ( \<Phi>(x)  \<^bold>\<leftrightarrow> ( \<lambda>y.  \<^bold>\<not>(y \<^bold>=\<^sup>Ly))(x) ))   ))) \<rfloor> "
  nitpick[user_axioms] oops

lemma ruff:  "\<lfloor>   \<^bold>\<diamond>  (  \<^bold>\<exists> \<Phi>. (BarcB (\<Phi>))) \<rfloor> "
  using nonempty BarcB_def BentzPrelimAttempt2 by metis


(* axiomatization where
dawgB:  "\<lfloor>  \<^bold>\<box> ( ( ( \<^bold>\<not> (Perfective1(B))  \<^bold>\<and>  (\<^bold>\<forall>\<^sup>Ex. ( B(x)  \<^bold>\<leftrightarrow> ( \<lambda>y.  \<^bold>\<not>(y \<^bold>=\<^sup>Ly))(x) ))   ))) \<rfloor> " *)

axiomatization where 
   trans: "transitive" 
   (* A2:  "\<lfloor>P(\<phi>) \<^bold>\<rightarrow>  \<^bold>\<box>(P (\<phi>))\<rfloor>" *)

(*Nitpicked with all permutations of A2 and A1*)
theorem T3: "\<lfloor> (\<^bold>\<exists>\<^sup>Ex. G3 x)\<rfloor>"
  nitpick[user_axioms] oops

axiomatization where 
   euc: "euclidean" 

lemma rudawg:  "\<lfloor>   \<^bold>\<box>  (  \<^bold>\<exists> \<Phi>. (BarcB (\<Phi>))) \<rfloor> "
  nitpick[user_axioms] oops
  (*using ruff HBcan euc trans refl nonempty by blast*)

(*Nitpicked with all permutations of A2 and A1*)
theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G3 x)\<rfloor>"
  nitpick[user_axioms] oops












axiomatization where 
    A1:  "\<lfloor>P(\<phi>) \<^bold>\<rightarrow>(P ( \<lambda>x.  ( \<^bold>\<box> (\<phi>(x)))))\<rfloor>" and
    GPDawg1 :  "\<lfloor> Perfective1(G1) \<rfloor>"  (*Note this is provable *)

(* Proof found using A1 ONLY *)
theorem TPrelim: "\<lfloor>\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( G3(x) \<^bold>\<rightarrow>  \<phi>(x) ))  \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.( \<^bold>\<box> ( G3(x) \<^bold>\<rightarrow>  \<phi>(x)) ))  \<rfloor>"
  using A1 euc trans refl Bentz2 Bentz3 BentzPrelimAttempt2 by blast

(*Proof found *)
theorem TPrelimSupp: "\<lfloor>Perfective1(\<phi>) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( G1(x) \<^bold>\<rightarrow>  \<phi>(x) )) \<rfloor>"
  using GPDawg1 G1_def Perfective1_def euc trans by blast

theorem TPrelimSupper: "\<lfloor> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( G3(x) \<^bold>\<rightarrow>  G1(x) )) \<rfloor>"
  using GPDawg1 Perfective1_def trans A1 helper3 refl euc by blast
(* ? ? ? ?*)
theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G3 x)\<rfloor>"
  using A1 euc trans refl Bentz2 Bentz3 BentzPrelimAttempt2 by blast

(* and  A2:  "\<lfloor>P(\<phi>) \<^bold>\<rightarrow>  \<^bold>\<box> (P (\<phi>))\<rfloor>" *)

subsection \<open>* Consistency again *\<close>

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


end
