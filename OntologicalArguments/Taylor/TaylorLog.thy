theory TaylorLog
imports Main "../QML_var"

begin

(*Note sigma sends individuals to bool typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals" *)

section \<open>* Anderson's Ontological Argument -- varying domain (individuals) *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  
abbreviation strctimpl :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "J" 49) where "\<phi> J \<psi> \<equiv> (\<lambda>w. (\<^bold>\<box> (\<phi>  \<^bold>\<rightarrow>  \<psi>)) w )"
            
definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
     
definition G0 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G0 x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi>  \<^bold>\<rightarrow>  \<Phi> x )"    
            
definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi>  \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"             
            
definition NotEq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where
  "NotEq x y \<equiv> \<^bold>\<not>(x \<^bold>=\<^sup>L y)"
  
  
consts H :: "\<mu> \<Rightarrow> \<sigma>"
consts K :: "\<mu> \<Rightarrow> \<sigma>"
consts D :: "\<mu> \<Rightarrow> \<sigma>"
  
definition DL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DL (x) \<equiv> \<^bold>\<not>(D(x))"  
    
definition Perfective1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))"  
    
definition Perfective2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"      
  
definition Perfective ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"
    

subsection \<open>* Consistency *\<close>

  lemma True 
    nitpick [satisfy, user_axioms, expect = genuine] oops
      
subsection \<open>* HOL *\<close>
    
(*Proof found *)    
theorem TE: "\<lfloor>\<^bold>\<not> (\<^bold>\<forall>\<Phi>. (\<^bold>\<not>(\<^bold>\<forall>\<^sup>Ex.  \<Phi> x  \<^bold>\<leftrightarrow>  (eiw x) ) ))\<rfloor>"
    by metis     

(*Proof found,/nitpick failed *)    
theorem Taut: " L \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
section \<open>* Perfective *\<close>    
 
axiomatization where refl: "x r x"
axiomatization where sym: "x r y \<longrightarrow> y r x"  
axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
  
lemma PConjun: "\<lfloor> Perfective(\<phi>)  \<^bold>\<leftrightarrow> (Perfective1(\<phi>) \<^bold>\<and> Perfective2(\<phi>)) \<rfloor>"
  using Perfective1_def Perfective2_def Perfective_def by presburger

  
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  apply (metis DL_def Perfective1_def)
  prf
  done

lemma PN: "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  nitpick oops

lemma PN1: "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  nitpick oops

lemma Giv2: "\<lfloor>Perfective2 DL\<rfloor>"
  nitpick[user_axioms] oops
    
    
subsection \<open>* Perfective -Variant3 *\<close>      
    
axiomatization where euc: "(\<forall>x y z. ((x r y) \<and> (x r z) \<longrightarrow> (y r z)))"
  
definition PerfectiveV31 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV31 (\<phi>)  \<equiv> ((\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x)))  J  D(x) ) ))"  
    
definition PerfectiveV32 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV32 (\<phi>)  \<equiv>  \<^bold>\<not> ( (\<^bold>\<exists>\<^sup>Ex.( \<phi>(x)  J  D(x) )))"      
  
definition PerfectiveV3 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV3 (\<phi>)  \<equiv>  PerfectiveV31 (\<phi>)  \<^bold>\<and>   PerfectiveV32 (\<phi>)"    
    
definition G_V3 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G_V3 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV3 \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
     
definition G0_V3 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G0_V3 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV3  \<Phi>  \<^bold>\<rightarrow>  \<Phi> x )"    
            
definition G1_V3 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1_V3 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV3 \<Phi>  \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"      
    
    
lemma Anderson1Var3:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((PerfectiveV3 \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (PerfectiveV3 (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  using PerfectiveV31_def PerfectiveV32_def PerfectiveV3_def nonempty by fastforce
  
lemma  Anderson2Var3:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (PerfectiveV3 \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> PerfectiveV3 \<Psi>))\<rfloor>" 
  nitpick[user_axioms] oops
    
axiomatization where Prop: "\<lfloor>PerfectiveV3(H)\<rfloor>"
  
axiomatization where PNV3: "\<lfloor>PerfectiveV3(\<phi>) \<^bold>\<rightarrow> (PerfectiveV3 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  
theorem Gawd : "\<lfloor>PerfectiveV3(G0_V3)\<rfloor> " 
  nitpick[user_axioms] oops
    
    
    
subsection \<open>* Perfective -Variant4 *\<close>   
    
definition PerfectiveV41 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV41 (\<phi>)  \<equiv> ((\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x)))  J  D(x) ) ))"  
    
definition PerfectiveV42 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV42 (\<phi>)  \<equiv>  \<^bold>\<not> ( (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x)  J  D(x) )))"      
  
definition PerfectiveV4 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV4 (\<phi>)  \<equiv>  PerfectiveV41 (\<phi>)  \<^bold>\<and>   PerfectiveV42 (\<phi>)"    
    
definition G_V4 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G_V4 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV4 \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
     
definition G0_V4 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G0_V4 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV4  \<Phi>  \<^bold>\<rightarrow>  \<Phi> x )"    
            
definition G1_V4 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1_V4 x \<equiv> \<^bold>\<forall>\<Phi>.( PerfectiveV4 \<Phi>  \<^bold>\<rightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"        
    
    
lemma Anderson1Var4:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((PerfectiveV4 \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (PerfectiveV4 (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  using PerfectiveV41_def PerfectiveV42_def PerfectiveV4_def nonempty by fastforce
  
lemma  Anderson2Var4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (PerfectiveV4 \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> PerfectiveV4 \<Psi>))\<rfloor>" 
  nitpick[user_axioms] oops    
    
axiomatization where 
             PropV4: "\<lfloor>PerfectiveV4(K)\<rfloor>" and
             PNV4: "\<lfloor>PerfectiveV4(\<phi>) \<^bold>\<rightarrow> (PerfectiveV4 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  
theorem Gawd : "\<lfloor>PerfectiveV4(G1_V4)\<rfloor> " 
  nitpick[user_axioms] oops    

(*Section:  Perfective V2*) 

consts OP :: "\<mu> \<Rightarrow> \<sigma>"

definition DN :: "\<mu> \<Rightarrow> \<sigma>" where
  " DN (x) \<equiv> \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( OP(y)) ))(x)  )"
  
definition DNL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNL (x) \<equiv> \<^bold>\<not>(DN(x))"  
    
definition Pn1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))"  
    
definition Pn2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"      
  
definition PerfectiveV2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV2 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"


lemma PN1Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
nitpick [user_axioms, show_all] oops


lemma PN2Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
 nitpick [user_axioms] oops

subsection \<open>* Perfective V2- For Consistency *\<close>
   
consts c :: "\<mu>" (* A constant symbol *)

axiomatization where
  Universal: "\<lfloor> \<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. x \<^bold>=\<^sup>L c) \<rfloor>"
  
axiomatization where 
  DefOP: " OP(x) \<equiv>  (x \<^bold>=\<^sup>L c) "
  
lemma Gib: "\<lfloor>Pn1 DNL\<rfloor>"
  apply (metis DNL_def Pn1_def)
  prf
  done

(*Proof found *)
lemma Gob: "\<lfloor>Pn2 DNL\<rfloor>" 

  by (metis Anderson_var.refl DNL_def DN_def DefOP Pn2_def Universal)  
    
lemma GibGob: "\<lfloor>PerfectiveV2 DNL\<rfloor>" 
  using DNL_def Gob PerfectiveV2_def Pn2_def by force
    
    
lemma PN1Cons: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
proof-
  fix w:: i
  fix v:: i
    
  {  
    assume rel: "w r v"
 
    assume Pef: "PerfectiveV2(\<phi>) w" 
      
  fix b:: \<mu>
      assume " v \<^bold>\<Turnstile> (\<^bold>\<exists>\<^sup>Ex. x \<^bold>=\<^sup>L b)" (*Also  works for  w \<^bold>\<Turnstile> (\<^bold>\<exists>\<^sup>Ex. x \<^bold>=\<^sup>L b) *)
 {   
      assume sp:  "v  \<^bold>\<Turnstile> (\<^bold>\<not>((\<lambda>x. \<^bold>\<box> (\<phi>(x))) b)) "
      then have tee: "\<exists>z. (v r z \<and>  (z  \<^bold>\<Turnstile>  (\<^bold>\<not>(\<phi>(b))) ))"
        by auto
  
    fix z::i 
        assume wit : "(v r z \<and>  (z  \<^bold>\<Turnstile>  (\<^bold>\<not>(\<phi>(b))) )) "
          
      have tot: "\<exists>(k ::i). (w r k \<and>  (k  \<^bold>\<Turnstile>  (\<^bold>\<exists>\<^sup>Ex. (\<phi>(x)  \<^bold>\<and> (\<^bold>\<not> (DN(x))) \<^bold>\<and> OP(x)) )   )  )"
        using Pef PerfectiveV2_def DN_def refl by metis   (*Proof found >1.0s; 2016 version *)
          
      have bij: " w r z "   
        using trans rel wit by metis
       
      then have dawg: "( (z  \<^bold>\<Turnstile> DN(b) ) ) " 
      proof -
        have f1: "\<lfloor>\<lambda>i. \<forall>m. (i \<^bold>\<Turnstile> OP m \<or> (\<exists>p. i \<^bold>\<Turnstile> (\<^sup>\<not>p) c \<and> i \<^bold>\<Turnstile> p m)) \<and> ((\<forall>p. i \<^bold>\<Turnstile> p c \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) m) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>OP) m)\<rfloor>"
          by (metis DefOP)
        obtain mm :: "i \<Rightarrow> \<mu>" and mma :: "i \<Rightarrow> \<mu>" where
          f2: "\<lfloor>\<lambda>i. \<lfloor>\<lambda>ia. i \<^bold>\<Turnstile> \<^bold>\<not> ((r) ia) \<or> (\<forall>p. i \<^bold>\<Turnstile> (\<^sup>\<not>p) (mm i) \<or> i \<^bold>\<Turnstile> p c) \<and> i \<^bold>\<Turnstile> eiw (mm i)\<rfloor>\<rfloor>"
          using Universal by moura
        moreover
        { assume "z \<^bold>\<Turnstile> eiw (mm z)"
          then have "z \<^bold>\<Turnstile> (OP b \<^bold>\<rightarrow> eiw b)"
            using f2 f1 Anderson_var.refl by fastforce
          then have ?thesis
            by (metis (full_types) Anderson_var.refl DN_def Pef PerfectiveV2_def bij wit) }
        ultimately show ?thesis
          using bij by blast
      qed (*Proof found 4.4s- e; 2016 version *)
          
      then have ice: "(v \<^bold>\<Turnstile> DN(b) ) "
        by (meson Anderson_var.trans DN_def wit) (*Proof found 31-185ms- all *)
        
    }
      
    hence epicwin: "v  \<^bold>\<Turnstile> ((\<^bold>\<not>((\<lambda>x. \<^bold>\<box> (\<phi>(x))) b))  \<^bold>\<rightarrow>  DN(b)) "
      by blast
          
  }
    
  then show ?thesis
     using PerfectiveV2_def Pn1_def by metis (* by metis; timeout >1s *)
qed
  
(*Proof found cvc4 *)
lemma PN1Cons2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>" 
  using Gob PN1Cons Pn1_def Pn2_def by fastforce 
    
    
subsection \<open>* Perfective V4- Correspondence *\<close>
  
axiomatization where 
  DefD: " D(x) \<equiv>   \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( G(y)) ))(x)  ) "
  
axiomatization where
  PNP: " \<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> (P (\<lambda>x. \<^bold>\<box> (\<Phi>(x)) )) )  )\<rfloor> " 
  
theorem PerfPN : "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  sorry
  (*nitpick [user_axioms, timeout =120] oops *)
  (* using DefD PNP Perfective_def Perfective1_def refl sym trans  by presburger *)
  

subsection \<open>* Immunity to Modal Collapse *\<close>  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.((\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)))\<rfloor>"
  nitpick [user_axioms, timeout =120] oops
    

end
