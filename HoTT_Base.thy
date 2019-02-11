(********
Isabelle/HoTT: Foundational definitions and notation
Feb 2019

This file is the starting point of the Isabelle/HoTT object logic, and contains the basic setup and definitions.
Among other things, it:

* Calls the setup of object-level type inference functionality.
* Defines the universe hierarchy and its governing rules.
* Defines named theorems for later use by proof methods.

********)

theory HoTT_Base
imports Pure
keywords
  "theorem*" "lemma*" "corollary*" "proposition*" :: thy_goal and
  "schematic_goal*" :: thy_goal

begin

section \<open>Terms and typing\<close>

typedecl t \<comment> \<open>Type of object-logic terms (which includes the types)\<close>

judgment has_type :: "[t, t] \<Rightarrow> prop"  ("(3_:/ _)")

section \<open>Setup non-core logic functionality\<close>

declare[[eta_contract=false]] \<comment> \<open>Do not eta-contract\<close>

ML \<open>val trace = Attrib.setup_config_bool @{binding "trace"} (K false)\<close>
  \<comment> \<open>Context attribute for tracing; use declare[[trace=true]] at any point in a theory to turn on.\<close>

text \<open>Set up type assumption and inference functionality:\<close>

ML_file "util.ML"
ML_file "typing.ML"

text \<open>
Set up keywords @{theory_text "theorem*"}, @{theory_text "lemma*"} etc.—theorem environments with type inference.
\<close>

ML \<open>
(* This code is copied and modified from the original in src/Pure/Pure.thy *)
let
val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem cmd schematic descr =
  Outer_Syntax.local_theory_to_proof' cmd ("State " ^ descr ^ " with type inference")
    ((long_statement || short_statement) >>
      (fn (long, binding, includes, elems, concl) =>
        (if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
          long Thm.theoremK NONE (K I) binding includes elems concl))
in
(
theorem @{command_keyword "theorem*"} false "theorem";
theorem @{command_keyword "lemma*"} false "lemma";
theorem @{command_keyword "corollary*"} false "corollary";
theorem @{command_keyword "proposition*"} false "proposition";
theorem @{command_keyword "schematic_goal*"} true "schematic goal"
)
end
\<close>
                                                                                  
section \<open>Universes\<close>

typedecl ord \<comment> \<open>Type of meta-numerals\<close>

axiomatization
  O   :: ord and
  Suc :: "ord \<Rightarrow> ord" and
  lt  :: "[ord, ord] \<Rightarrow> prop"  (infix "<" 999) and
  leq :: "[ord, ord] \<Rightarrow> prop"  (infix "\<le>" 999)
where
  lt_Suc: "n < (Suc n)" and
  lt_trans: "\<lbrakk>m1 < m2; m2 < m3\<rbrakk> \<Longrightarrow> m1 < m3" and
  leq_min: "O \<le> n"

declare
  lt_Suc [intro!]
  leq_min [intro!]
  lt_trans [intro]

axiomatization
  U :: "ord \<Rightarrow> t"
where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and
  U_cumulative: "\<lbrakk>A: U i; i < j\<rbrakk> \<Longrightarrow> A: U j" and
  U_cumulative': "\<lbrakk>A: U i; i \<le> j\<rbrakk> \<Longrightarrow> A: U j"

text \<open>
Using method @{method rule} with @{thm U_cumulative} and @{thm U_cumulative'} is unsafe: if applied blindly it will very easily lead to non-termination.
Instead use @{method elim}, or instantiate the rules suitably.

@{thm U_cumulative'} is an alternative rule used by the method @{theory_text cumulativity} in @{file HoTT_Methods.thy}.
\<close>

section \<open>Type families\<close>

abbreviation (input) constraint :: "[t \<Rightarrow> t, t, t] \<Rightarrow> prop"  ("(1_:/ _ \<leadsto> _)")
where "f: A \<leadsto> B \<equiv> (\<And>x. x: A \<Longrightarrow> f x: B)"

text \<open>We use the notation @{prop "B: A \<leadsto> U i"} to abbreviate type families.\<close>

section \<open>Named theorems\<close>

named_theorems form
named_theorems comp
named_theorems cong

text \<open>
The named theorems above will be used by proof methods defined in @{file HoTT_Methods.thy}.

@{attribute form} declares type formation rules.
These are mainly used by the \<open>cumulativity\<close> method, which lifts types into higher universes.

@{attribute comp} declares computation rules, which are used by the \<open>compute\<close> method, and may also be passed to invocations of the method \<open>subst\<close> to perform equational rewriting.

@{attribute cong} declares congruence rules, the definitional equality rules of the type theory.
\<close>

(* Todo: Set up the Simplifier! *)

end
