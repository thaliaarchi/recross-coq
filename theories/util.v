Require Export List. Export ListNotations.
Require Export Program.Equality.

Ltac invert H := inversion H; subst; clear H.