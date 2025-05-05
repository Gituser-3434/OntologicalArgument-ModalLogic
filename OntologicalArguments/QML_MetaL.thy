theory QML_MetaL
imports Main QML

begin
section \<open>* Varying Domains * \<close>

(* Technically, varying domains are encoded with 
        the help of an  existence relation expressing
        which individuals actually exist in each world.*)

  consts eiw :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
  axiomatization where nonempty: "\<forall>w. \<exists>x. eiw x w"


(* Actualistic quantifiers are 
        quantifiers guarded by the existence relation. *)

  abbreviation mforalle :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<forall>\<^sup>E")
         where "\<^bold>\<forall>\<^sup>E \<Phi> \<equiv> (\<lambda>w. \<forall>x. (eiw x w) \<longrightarrow> (\<Phi> x w))" 
  abbreviation mforalleB:: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (binder"\<^bold>\<forall>\<^sup>E"[8]9) 
        where "\<^bold>\<forall>\<^sup>E x. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E \<phi>"
  abbreviation mexistse :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<exists>\<^sup>E")
         where "\<^bold>\<exists>\<^sup>E \<Phi> \<equiv> (\<lambda>w. \<exists>x. (eiw x w) \<and> \<Phi> x w)" 
  abbreviation mexistseB :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (binder"\<^bold>\<exists>\<^sup>E"[8]9) 
    where "\<^bold>\<exists>\<^sup>E x. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E \<phi>"  

(*Proof found *)
lemma ExEss: "\<lfloor>\<^bold>\<forall>\<^sup>E y.  \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. (x \<^bold>=\<^sup>Ly)) \<^bold>\<rightarrow>   (\<^bold>\<exists>\<^sup>Ex. ( \<^bold>\<box> (x \<^bold>=\<^sup>Ly)))\<rfloor>"
  using nonempty by blast   

lemma Mov:  "\<lfloor>\<^bold>\<forall> \<Phi>.  \<^bold>\<box> (\<^bold>\<forall>\<^sup>E y. (\<^bold>\<not>(\<Phi>(y))) ) \<^bold>\<rightarrow>    (  (\<^bold>\<forall>\<^sup>Ey. ( \<^bold>\<box> (\<Phi>(y) \<^bold>\<rightarrow> \<^bold>\<not>(\<Phi>(y))))   ))\<rfloor>"
  nitpick[user_axioms] oops

lemma Mov2:  "(symmetric \<and> euclidean \<and> transitive \<and> reflexive) \<longrightarrow> \<lfloor>(\<^bold>\<forall> \<Phi>.  \<^bold>\<box> (\<^bold>\<forall>\<^sup>E y. (\<^bold>\<not>(\<Phi>(y))) ) \<^bold>\<rightarrow>    (  (\<^bold>\<forall>\<^sup>Ey. ( \<^bold>\<box> (\<Phi>(y) \<^bold>\<rightarrow> \<^bold>\<not>(\<Phi>(y))))   )))\<rfloor>"
  nitpick[user_axioms, card \<mu> = 2] oops

consts Ba :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" 
consts Bum :: "(\<mu> \<Rightarrow> \<sigma>)" 

(*Higher Order Barcan *)
lemma HBcan:  "\<lfloor> \<^bold>\<diamond> ( \<^bold>\<exists> \<Phi>.(Ba(\<Phi>) ) )  \<^bold>\<rightarrow> ( \<^bold>\<exists> \<Phi>. ( \<^bold>\<diamond> (Ba(\<Phi>) ) ) ) \<rfloor> "
  using nonempty by blast

lemma BcanPonies:  "(symmetric \<and> euclidean \<and> transitive \<and> reflexive) \<longrightarrow> \<lfloor>  ( \<^bold>\<diamond> ( \<^bold>\<exists> \<Phi>. (Ba(\<Phi>) ) )  \<^bold>\<rightarrow> ( \<^bold>\<box>  ( \<^bold>\<exists> \<Phi>.  \<^bold>\<diamond>(Ba(\<Phi>) ) ) ))  \<rfloor> " 
  using nonempty by metis

(*First-Order Barcan *)
lemma Barcan:  "\<lfloor>\<^bold>\<forall> \<Phi>.   ( \<^bold>\<diamond> ( \<^bold>\<exists>x. (\<Phi>(x) ) )  \<^bold>\<rightarrow> ( \<^bold>\<exists>x. ( \<^bold>\<diamond> (\<Phi>(x) ) ) )) \<rfloor> " 
  by auto

lemma Ponies:  "(symmetric \<and> euclidean \<and> transitive \<and> reflexive) \<longrightarrow> \<lfloor>  ( \<^bold>\<diamond> ( \<^bold>\<exists>x. (Bum(x) ) )  \<^bold>\<rightarrow> ( \<^bold>\<box>  (\<^bold>\<exists>x.  \<^bold>\<diamond>(Bum(x) ) ) ))  \<rfloor> " 
  using nonempty by metis


axiomatization where
  reflex: "reflexive" 
  
lemma BarEss: "\<lfloor>\<^bold>\<forall>\<Phi>.  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex. (\<Phi>(x) )) \<^bold>\<rightarrow>   (\<^bold>\<forall>\<^sup>Ex. ( \<^bold>\<box> (\<Phi>(x))))\<rfloor>"
  nitpick[user_axioms] oops

end
