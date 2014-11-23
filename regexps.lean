exit
/-
Regular expressions from Coq Syntax to Lean syntax. Contains lots of errors.
note: using emacs regexes (e.g. with \( and \)), except that \n should still be replaced by newlines (C-q C-j)
Note: some spaces might be wrong at the end or beginning of the following regexes
-/
([*][*]? [*]* ?\(\(.\|\n\)*?\)[*])              /- \1-/
Section \(.*?\)\.				section \1
Definition 					definition
Lemma                                           definition
Theorem                                         definition
Global Instance \([^ ]+\)			definition \1 [instance]
 *\n\( *\):=                                     :=\n\1
fun \(.*?\) ?=>                                 λ\1,
Proof\.\(\(.\|\n\)*?\)\(Defined\|Qed\)\.        /-begin\1end-/
`{\([^:]*?\)}                                   [H : \1]
 @                                               ⬝
 #                                               ▹
<~>                                             ≃
=                                               ≈
 o                                               ∘
 \*                                              ×
 ->                                              →
^[-1]?                                          ⁻¹
(\([^(),;]\{1,20\}\);\([^(),;]\{1,20\}\))       ⟨\1,\2⟩
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
forall                                          Π
 Contr                                          is_contr
 IsTrunc                                        is_trunc
 IsHProp                                        is_hprop
BuildEquiv                                      Equiv.mk
BuildIsEquiv                                    IsEquiv.mk
\([^a-zA-Z_.]\)pr\(1\|2\)\([^a-zA-Z_.]\)        \1dpr\2\3
\([^a-zA-Z_.]\)tt\([^a-zA-Z_.]\)                \1star\2
\([^a-zA-Z_.]\)Unit\([^a-zA-Z_.]\)              \1unit\2
\([^a-zA-Z_.]\)true\([^a-zA-Z_.]\)              \1tt\2
\([^a-zA-Z_.]\)false\([^a-zA-Z_.]\)             \1ff\2
\([^a-zA-Z_.]\)Bool\([^a-zA-Z_.]\)              \1bool\2
\([^a-zA-Z_.]\)fst\([^a-zA-Z_.]\)               \1pr1\2
\([^a-zA-Z_.]\)snd\([^a-zA-Z_.]\)               \1pr2\2
