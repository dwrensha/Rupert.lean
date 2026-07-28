module

public import Rupert.Basic
public import Rupert.Set
public import Rupert.Affine

@[expose] public section

proof_wanted affine_rupert_iff_rupert_set (X : Set (EuclideanSpace ℝ (Fin 3))) :  IsAffineRupertSet X ↔ IsRupertSet X
