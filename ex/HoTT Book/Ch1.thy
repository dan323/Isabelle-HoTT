theory Ch1
  imports "../../HoTT"
begin

chapter \<open>HoTT Book, Chapter 1\<close>

section \<open>1.6 Dependent pair types (\<Sigma>-types)\<close>

text "Prove that the only inhabitants of the \<Sigma>-type are those given by the pair constructor."

schematic_goal
  assumes "(\<Sum>x:A. B(x)): U(i)" and "p: \<Sum>x:A. B(x)"
  shows "?a: p =[\<Sum>x:A. B(x)] <fst p, snd p>"

text "Proof by induction on \<open>p: \<Sum>x:A. B(x)\<close>:"

proof (rule Sum_elim[where ?p=p])
  text "We just need to prove the base case; the rest will be taken care of automatically."

  fix x y assume asm: "x: A" "y: B(x)" show
    "refl(<x,y>): <x,y> =[\<Sum>x:A. B(x)] <fst <x,y>, snd <x,y>>"
  proof (subst (0 1) comp)
    text "
      The computation rules for \<open>fst\<close> and \<open>snd\<close> require that \<open>x\<close> and \<open>y\<close> have appropriate types.
      The automatic proof methods have trouble picking the appropriate types, so we state them explicitly,
    "
    show "x: A" and "y: B(x)" by (fact asm)+

    text "...twice, once each for the substitutions of \<open>fst\<close> and \<open>snd\<close>."
    show "x: A" and "y: B(x)" by (fact asm)+

  qed (derive lems: assms asm)

qed (derive lems: assms)


end