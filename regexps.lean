exit
/-
Regular expressions from Coq Syntax to Lean syntax. Contains lots of errors.
note: using emacs regexps (e.g. with \( and \)), except that \n should still be replaced by newlines (C-q C-j)
-/
([*][*]? [*]* ?\(\(.\|\n\)*?\)[*])              /- \1-/
Section \(.*?\)\.				section \1
Definition 					definition
Glocal Instance \([^ ]+\)			definition \1 [instance]
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
\([^a-zA-Z_]\)pr\(1\|2\)\([^a-zA-Z_]\)          \1dpr\2\3
\([^a-zA-Z_]\)tt\([^a-zA-Z_]\)                  \1star\2
\([^a-zA-Z_]\)Unit\([^a-zA-Z_]\)                \1unit\2
\([^a-zA-Z_]\)true\([^a-zA-Z_]\)                \1tt\2
\([^a-zA-Z_]\)false\([^a-zA-Z_]\)               \1ff\2
\([^a-zA-Z_]\)Bool\([^a-zA-Z_]\)                \1bool\2
