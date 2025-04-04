theory Taylor_var
imports Main "../QML_var"

begin

(*Note sigma sends individuals to bool typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals" *)

section \<open>* Taylor's Simplified Ontological Argument -- varying domain (individuals) *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"          
  
consts H :: "\<mu> \<Rightarrow> \<sigma>"

axiomatization where
    M1:  "\<exists>x y.  x r x \<and> x\<noteq>y" and (*More than one world *)
    M2:  "\<exists>w. (w r w) \<and> ((\<^bold>\<exists>\<^sup>Ex. (\<^bold>\<exists>\<^sup>Ey. (\<^bold>\<not>(x \<^bold>=\<^sup>L y))) ) w)"   (*world with more than one individual *)
    

consts D :: "\<mu> \<Rightarrow> \<sigma>" 
  
definition DL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DL (x) \<equiv> \<^bold>\<not>(D(x))"  
    
definition Perfective1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))"  
    
definition Perfective2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"      
  
definition Perfective ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"
    
definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
      
definition G0 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G0 x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective \<Phi> \<^bold>\<rightarrow>  ( ((\<Phi> x ))) )"                   
            
definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 x \<equiv> \<^bold>\<forall>\<Phi>.( Perfective \<Phi> \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"      
    
    
(*Basic Results *)    
    
lemma PConjun: "\<lfloor> Perfective(\<phi>)  \<^bold>\<leftrightarrow> (Perfective1(\<phi>) \<^bold>\<and> Perfective2(\<phi>)) \<rfloor>"
  using Perfective1_def Perfective2_def Perfective_def by presburger
  
    
(*Note that the Isar proof works for when D is simply a consts*)    
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  apply (metis DL_def  Perfective1_def)
  prf
  done
    
  (*proof -
  obtain ii :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i" where
    "\<lfloor>\<lambda>x0. \<forall>x1. x0 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>v2. \<exists>v3. (v2 \<^bold>\<Turnstile> eiw v3 \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3) = (ii x0 x1 \<^bold>\<Turnstile> op r x0 \<and> (\<exists>v3. (ii x0 x1 \<^bold>\<Turnstile> eiw v3 \<and> ii x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> ii x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3))\<rfloor>"
    by moura
  then obtain mm :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<mu>" where
    "\<forall>p. \<lfloor>\<lambda>i. (i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective1 p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> p m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor>) \<and> (i \<^bold>\<Turnstile> Perfective1 p \<or> ii i p \<^bold>\<Turnstile> op r i \<and> (ii i p \<^bold>\<Turnstile> eiw (mm i p) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>p) (mm i p)) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mm i p))\<rfloor>"
    by (metis (full_types) Perfective1_def)
  then show ?thesis
    by (metis (full_types) DL_def)
qed*)    
    
  
axiomatization where
    A1:  "\<lfloor>Perfective (H)\<rfloor>"  and
    A2:  "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"  

subsection \<open>* Consistency *\<close>

  lemma True 
    nitpick [satisfy, user_axioms, expect = genuine] oops
      
subsection \<open>* HOL *\<close>

(*Proof found,/nitpick failed *)
theorem Pred: "\<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> x \<^bold>\<leftrightarrow>  (\<^bold>\<exists>\<^sup>Ey. (x \<^bold>=\<^sup>L y) ))\<rfloor>"
  using nonempty by blast

(* proof -
  obtain ii :: i where
    f1: "(\<exists>X0. \<forall>x1. (X0 \<^bold>\<Turnstile> (\<^sup>\<not>x1) x \<or> (\<forall>A_x. X0 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) A_x \<or> (\<exists>x3. X0 \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> X0 \<^bold>\<Turnstile> x3 x))) \<and> (X0 \<^bold>\<Turnstile> x1 x \<or> (\<exists>x4. X0 \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. X0 \<^bold>\<Turnstile> x5 x4 \<or> X0 \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)))) \<longrightarrow> (\<forall>x1. (ii \<^bold>\<Turnstile> (\<^sup>\<not>x1) x \<or> (\<forall>A_x. ii \<^bold>\<Turnstile> (\<^sup>\<not>eiw) A_x \<or> (\<exists>x3. ii \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> ii \<^bold>\<Turnstile> x3 x))) \<and> (ii \<^bold>\<Turnstile> x1 x \<or> (\<exists>x4. ii \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 x4 \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x))))"
    by metis
  obtain bb :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
    f2: "\<forall>A_x. (\<exists>x3. ii \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> ii \<^bold>\<Turnstile> x3 x) \<longrightarrow> ii \<^bold>\<Turnstile> (\<^sup>\<not>bb A_x) A_x \<and> ii \<^bold>\<Turnstile> bb A_x x"
    by moura
  obtain mm :: \<mu> where
    f3: "(\<exists>x4. ii \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 x4 \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)) \<longrightarrow> ii \<^bold>\<Turnstile> eiw mm \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 mm \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)"
    by presburger
  have "\<exists>p. ii \<^bold>\<Turnstile> p x \<and> (\<exists>m. ii \<^bold>\<Turnstile> eiw m \<and> (ii \<^bold>\<Turnstile> bb m m \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>bb m) x)) \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>p) x \<and> (ii \<^bold>\<Turnstile> (\<^sup>\<not>eiw) mm \<or> (\<exists>p. ii \<^bold>\<Turnstile> (\<^sup>\<not>p) mm \<and> ii \<^bold>\<Turnstile> p x))"
    by meson (* > 1.0 s, timed out *)
  then have "\<lfloor>\<lambda>i. \<exists>p. i \<^bold>\<Turnstile> p x \<and> (\<exists>m. i \<^bold>\<Turnstile> eiw m \<and> (\<forall>p. i \<^bold>\<Turnstile> p m \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) x)) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) x \<and> (\<forall>m. i \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> (\<exists>p. i \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<and> i \<^bold>\<Turnstile> p x))\<rfloor>"
    using f3 f2 f1 by moura (* > 1.0 s, timed out *)
  then show ?thesis
    by (metis (no_types))
qed*)

(*Proof found,/nitpick failed *)    
theorem Taut: " L \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
subsection \<open>* Anderson *\<close>   

lemma Giv2: "\<lfloor>Perfective2 DL\<rfloor>"
  nitpick[user_axioms] oops
    
(*Proof found after <1 s *)    
lemma Anderson1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((Perfective \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (Perfective (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  using Perfective_def by presburger
  
lemma  Anderson2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (Perfective \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> Perfective \<Psi>))\<rfloor>" 
  apply (metis Perfective1_def Perfective2_def PConjun) 
  prf
  done
  
(*Subsection: Provability of Theorems *)
  
  (*Proof found <136ms*)
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( Perfective \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  apply (metis Anderson1 Anderson2)
  prf
  done
  
   (*Proof found >1s & 8.6s *)
   lemma G0L: "\<lfloor>Perfective (G0)\<rfloor>"
    using Perfective1_def Perfective2_def PConjun A1 by blast
  (* proof -
    have f1: "\<forall>p. \<lfloor>\<lambda>i. i \<^bold>\<Turnstile> Perfective p = (\<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> p m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor> \<and> i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> (eiw m \<^bold>\<and> p m) \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>D) m))\<rfloor>"
      using Perfective_def by auto
    obtain ii :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i" where
          "\<lfloor>\<lambda>x0. \<forall>x1. x0 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>v2. \<exists>v3. v2 \<^bold>\<Turnstile> (eiw v3 \<^bold>\<and> x1 v3) \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3) = (ii x0 x1 \<^bold>\<Turnstile> op r x0 \<and> (\<exists>v3. ii x0 x1 \<^bold>\<Turnstile> (eiw v3 \<^bold>\<and> x1 v3) \<and> ii x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3))\<rfloor>"
      by moura
    then obtain mm :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<mu>" where
      f2: "\<lfloor>\<lambda>i. \<forall>p. i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> (eiw m \<^bold>\<and> p m) \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>D) m) = (ii i p \<^bold>\<Turnstile> op r i \<and> ii i p \<^bold>\<Turnstile> (eiw (mm i p) \<^bold>\<and> p (mm i p)) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mm i p))\<rfloor>"
      by (metis (no_types))
    obtain mma :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<mu>" where
      f3: "\<lfloor>\<lambda>x0. \<forall>x1. (\<exists>v3. (v2_4 x0 x1 \<^bold>\<Turnstile> eiw v3 \<and> v2_4 x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> v2_4 x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3) = ((v2_4 x0 x1 \<^bold>\<Turnstile> eiw (mma x0 x1) \<and> v2_4 x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>x1) (mma x0 x1)) \<and> v2_4 x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) (mma x0 x1))\<rfloor>"
      by moura
    obtain iia :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i" where
    "\<lfloor>\<lambda>x0. \<forall>x1. x0 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>v2. \<exists>v3. (v2 \<^bold>\<Turnstile> eiw v3 \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3) = (iia x0 x1 \<^bold>\<Turnstile> op r x0 \<and> (\<exists>v3. (iia x0 x1 \<^bold>\<Turnstile> eiw v3 \<and> iia x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> iia x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3))\<rfloor>"
    by moura
  then have "\<lfloor>\<lambda>i. \<forall>p. i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. (i \<^bold>\<Turnstile> eiw m \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>p) m) \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>D) m) = (iia i p \<^bold>\<Turnstile> op r i \<and> (iia i p \<^bold>\<Turnstile> eiw (mma i p) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>p) (mma i p)) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mma i p))\<rfloor>"
    using f3 by presburger
  then have f4: "\<lfloor>\<lambda>i. \<forall>p. (i \<^bold>\<Turnstile> Perfective p = (\<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> p m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor> \<and> i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> (eiw m \<^bold>\<and> p m) \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>D) m))) = ((i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> p m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor> \<and> ii i p \<^bold>\<Turnstile> op r i \<and> ii i p \<^bold>\<Turnstile> (eiw (mm i p) \<^bold>\<and> p (mm i p)) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mm i p)) \<and> (i \<^bold>\<Turnstile> Perfective p \<or> iia i p \<^bold>\<Turnstile> op r i \<and> (iia i p \<^bold>\<Turnstile> eiw (mma i p) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>p) (mma i p)) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mma i p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> (\<^sup>\<not>p) m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor>))\<rfloor>"
    using f2 by meson
  have "\<forall>x0. \<lfloor>\<lambda>x1. \<forall>x3. ((x1 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) x0 \<or> x1 \<^bold>\<Turnstile> (\<^sup>\<not>x3) x0) \<or> x1 \<^bold>\<Turnstile> D x0) = (x1 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) x0 \<or> x1 \<^bold>\<Turnstile> (\<^sup>\<not>x3) x0 \<or> x1 \<^bold>\<Turnstile> D x0)\<rfloor>"
    by meson
      then have f5: "\<forall>p. \<lfloor>\<lambda>i. (i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> (p m \<^bold>\<or> D m))\<rfloor> \<and> ii i p \<^bold>\<Turnstile> op r i \<and> ii i p \<^bold>\<Turnstile> eiw (mm i p) \<and> ii i p \<^bold>\<Turnstile> p (mm i p) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mm i p)) \<and> (i \<^bold>\<Turnstile> Perfective p \<or> iia i p \<^bold>\<Turnstile> op r i \<and> iia i p \<^bold>\<Turnstile> eiw (mma i p) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>p) (mma i p) \<and> iia i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mma i p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<or> ia \<^bold>\<Turnstile> D m)\<rfloor>)\<rfloor>"
        using f4 f1 by simp
      have "iia v0_0 G0 \<^bold>\<Turnstile> op r v0_0 \<and> iia v0_0 G0 \<^bold>\<Turnstile> eiw (mma v0_0 G0) \<and> iia v0_0 G0 \<^bold>\<Turnstile> (\<^sup>\<not>G0) (mma v0_0 G0) \<and> iia v0_0 G0 \<^bold>\<Turnstile> (\<^sup>\<not>D) (mma v0_0 G0) \<longrightarrow> iia v0_0 G0 \<^bold>\<Turnstile> op r (iia v0_0 G0)"
        using Taylor_var.sym Taylor_var.trans by blast
      then have f6: "iia v0_0 G0 \<^bold>\<Turnstile> \<^bold>\<not> (op r v0_0) \<or> iia v0_0 G0 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) (mma v0_0 G0) \<or> iia v0_0 G0 \<^bold>\<Turnstile> (G0 (mma v0_0 G0) \<^bold>\<or> D (mma v0_0 G0))"
        using f5 by (metis (full_types) G0_def)
      have f7: "ii v0_0 H \<^bold>\<Turnstile> op r (ii v0_0 H)"
        using f5 by (metis (no_types) A1 Taylor_var.sym Taylor_var.trans)
      obtain iib :: i where
        "(\<exists>v0. v0 \<^bold>\<Turnstile> \<^bold>\<not> (Perfective G0)) = iib \<^bold>\<Turnstile> \<^bold>\<not> (Perfective G0)"
        by blast
      then show ?thesis
        using f7 f6 f5 by (metis (no_types) A1 G0_def)
    qed *)
  
axiomatization where reflex: "x r x"

lemma ExEss: "\<lfloor>\<^bold>\<forall>\<^sup>E y.  \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. (x \<^bold>=\<^sup>Ly)) \<^bold>\<rightarrow>   (\<^bold>\<exists>\<^sup>Ex. ( \<^bold>\<box> (x \<^bold>=\<^sup>Ly)))\<rfloor>"
  using refl by blast
  
lemma EqG : " \<lfloor> G0 x \<^bold>\<leftrightarrow>  G1 x\<rfloor>"    
  using A2 G0_def G1_def Taylor_var.reflex by fastforce
    
theorem Anderson3 : " \<lfloor>Perfective  G1\<rfloor>"    
  using Anderson2 EqG G0L by blast
      
corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G1 x)\<rfloor>"
    using Anderson3 T1 by auto
  
lemma EP: "\<lfloor>Perfective eiw\<rfloor>" (*Existence is positive *)
  apply (metis A1 Anderson2)
  prf
  done
  (*proof -
    { fix ii :: i
      have "\<lfloor>\<lambda>i. \<forall>p pa. (i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective p) \<or> i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> eiw m \<and> i \<^bold>\<Turnstile> p m \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>pa) m)) \<or> i \<^bold>\<Turnstile> Perfective pa\<rfloor>"
        by (metis Anderson2)
      then have "ii \<^bold>\<Turnstile> P eiw"
        using A3 by blast }
    then show ?thesis
      by auto
  qed*)

corollary C2: "\<lfloor>Perfective  (\<lambda>x. \<^bold>\<box> (eiw(x)) )\<rfloor>"     
  using A2 EP by blast
    
axiomatization where euc: "euclidean"  
      
theorem T2: "\<lfloor> \<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G1 x)\<rfloor>"
  by (metis Anderson3 C1 EP G1_def euc)


subsection \<open>* Consistency again *\<close>

lemma True 
    nitpick [satisfy, user_axioms, timeout = 30, expect = genuine] oops
      
subsection \<open>* Immunity to Modal Collapse *\<close>  
 
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.((\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)))\<rfloor>"
  nitpick [user_axioms, card \<mu> =2, show_all] oops


end
