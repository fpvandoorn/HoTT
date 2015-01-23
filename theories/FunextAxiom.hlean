/- To assume the funext axiom outright, import this file.
    (Doing this instead of simply positing funext directly
    avoids creating multiple witnesses for the axiom in
    different developments.) -/

Require Import Basics.Overture.

Axiom funext_axiom : funext.
Global Existing Instance funext_axiom.
