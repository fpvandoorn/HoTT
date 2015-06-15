
exit

/-
Regular expressions from Coq Syntax to Lean syntax. Contains lots of errors.
note: using emacs regexes (e.g. with \( and \)), except that \n should still be replaced by newlines (C-q C-j)
Note: some spaces might be wrong at the end or beginning of the following regexes

--------------
Instructions to apply a single regular expression to multiple files:
open emacs
M-x find_dired
fill in directory (e.g. ~/projects/HoTT/theories) (this includes subdirectories)
fill out which files (e.g. -name "*.v" for Coq files)
In the *Find* buffer, mark which files you want to search
  (e.g. *@t for all but temporary files or %g<RET> for all files)
Press Q to do regexp replace
Press Y to apply regexp to all marked buffers
Go to *Find* buffer again for another regexp (C-x b Find<RET>) --or--
to save all files, list all buffers with M-x ibuffer
to save all files: *uS
to kill all marked files: D
-------------
notes about converting Coq tactics:
equiv_intro is basically equiv_rect + intro
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
 o                                               ∘
 \*                                              ×
 ->                                              →
^[-1]?                                          ⁻¹
 ==                                              ∼
(\([^(),;]\{1,20\}\);\([^(),;]\{1,20\}\))       ⟨\1,\2⟩
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
{ ?\([^{&}]*?\) & \([^{&}]*?\)}                 Σ\1, \2
 Contr                                          is_contr
 IsTrunc                                        is_trunc
 IsHProp                                        is_hprop
BuildEquiv                                      equiv.mk
BuildIsEquiv                                    is_equiv.mk
_forall_                                        _pi_
Funext                                          funext
\([^a-zA-Z_.]\)forall\(1\|2\)\([^a-zA-Z_.]\)    \1Π\2
\([^a-zA-Z_.]\)pr\(1\|2\)\([^a-zA-Z_.]\)        \1dpr\2\3
\([^a-zA-Z_.]\)tt\([^a-zA-Z_.]\)                \1star\2
\([^a-zA-Z_.]\)Unit\([^a-zA-Z_.]\)              \1unit\2
\([^a-zA-Z_.]\)true\([^a-zA-Z_.]\)              \1tt\2
\([^a-zA-Z_.]\)false\([^a-zA-Z_.]\)             \1ff\2
\([^a-zA-Z_.]\)Bool\([^a-zA-Z_.]\)              \1bool\2
\([^a-zA-Z_.]\)fst\([^a-zA-Z_.]\)               \1pr1\2
\([^a-zA-Z_.]\)snd\([^a-zA-Z_.]\)               \1pr2\2
\([^a-zA-Z_.]\)IsEquiv\([^a-zA-Z_.]\)           \1is_equiv\2
\([^a-zA-Z_.]\)eisretr\([^a-zA-Z_.]\)           \1retr\2
\([^a-zA-Z_.]\)eissect\([^a-zA-Z_.]\)           \1sect\2
\([^a-zA-Z_.]\)eisadj\([^a-zA-Z_.]\)            \1adj\2
\([^a-zA-Z_.]\)idpath\([^a-zA-Z_.]\)            \1refl\2
