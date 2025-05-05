theory Bin_b_1
imports Main "../QML_var"

begin

(*Note sigma sends individuals to bool typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals" *)

section \<open>* Modified Bentzmuller Simplified Ontological Argument -- varying domain (individuals) *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"          

definition G3 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G3 x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( ( (\<Phi> x ))) )"


consts D :: "\<mu> \<Rightarrow> \<sigma>" 
  
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
            "G0 x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective1(\<Phi>) \<^bold>\<rightarrow>  ( ((\<Phi> x ))) )"                   
            
definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective1 \<Phi> \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"      
    
definition G1P :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1P x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )" 

definition GP :: "\<mu> \<Rightarrow> \<sigma>" where 
            "GP x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  

(*Basic Results *)    
  
    
(*Note that the Isar proof works for when D is simply a consts*)    
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  apply (metis DL_def Perfective1_def)
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

lemma helper4:  "\<lfloor> Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx))   \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex. (x \<^bold>=\<^sup>Lx)  \<^bold>\<rightarrow> D(x) )  \<rfloor>" 
  using refl Perfective1_def by metis

lemma helper5:  "\<lfloor> Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx))   \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex. D(x) )  \<rfloor>" 
  using refl Perfective1_def by metis

lemma BentzPrelim : "\<lfloor>   \<^bold>\<diamond>  ( \<^bold>\<not> (Perfective1( \<lambda>x. \<^bold>\<not>(x \<^bold>=\<^sup>Lx)))) \<rfloor> "
  nitpick[user_axioms] oops

lemma Bentz3 :  "\<lfloor> Perfective1(G0) \<rfloor>"  
  using G0_def Bentz2 Giv by metis

axiomatization where
PushinP: "\<lfloor>  \<^bold>\<box> ( \<^bold>\<exists> \<Phi>. (    ( \<^bold>\<not> (Perfective1( \<Phi>))  \<^bold>\<and>  (\<^bold>\<forall>\<^sup>Ex. ( \<Phi>(x)  \<^bold>\<leftrightarrow> ( \<lambda>y.  \<^bold>\<not>(y \<^bold>=\<^sup>Ly))(x) ))   ))) \<rfloor> " 


(*Proof Found*)
theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G0 x)\<rfloor>"
  using PushinP Bentz3 Bentz2 Giv refl by blast


subsection \<open>* Consistency again *\<close>

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


end
