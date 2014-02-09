(* Copyright (c) 2014, Robert Dockins *)

(**  Reserved notation declarations gathered in one place to help
     debug parsing problems, etc.
  *)

Reserved Notation "x ≈ y" (at level 70).
Reserved Notation "x ≉ y" (at level 70).
Reserved Notation "x ≤ y" (at level 70).
Reserved Notation "y ≥ x" (at level 70).
Reserved Notation "x ≰ y" (at level 70).
Reserved Notation "y ≱ x" (at level 70).

Reserved Notation "x ∘ y"
  (at level 40, left associativity,
  format
    "'[hv' x  '∘' '/'  y ']'").

Reserved Notation "〈 f , g 〉" 
  (format
    "'[hv' '〈' f '/' ','  g '/' '〉' ']'"
  ). 

Reserved Notation "《 f , g 》" 
  (format
    "'[hv' '《' f '/' ','  g '/' '》' ']'"
  ). 

Reserved Notation "'Λ' f" 
  (f at next level, at level 0,
  format
    "'[hv' 'Λ' f ']'"
  ).

Reserved Notation "〚 x 〛"
  (format
    "'[hv' '〚'  x  '〛' ']'"
  ). 

Reserved Notation "x ∈ X" (at level 60).
Reserved Notation "x ∉ X"  (at level 60).
Reserved Notation "X ⊆ Y" (at level 66).
Reserved Notation "∪ XS" (at level 50).
Reserved Notation "∅".

Reserved Notation "∐ XS"  (at level 10).
Reserved Notation "⊥".
Reserved Notation "∗".

Reserved Notation "'id'".
Reserved Notation "'id' ( A )" (format "'id' '(' A ')'").
Reserved Notation "'Id'".
Reserved Notation "'Id' ( A )" (format "'Id' '(' A ')'").

Reserved Notation "A → B" (at level 65).
Reserved Notation "A ↣ B" (at level 65).
Reserved Notation "A ↠ B" (at level 65).
Reserved Notation "A ↔ B" (at level 65).

Reserved Notation "'!'".
Reserved Notation "'¡'".

Reserved Notation "f '⁻¹'" (at level 1, format "f '⁻¹'").

Reserved Notation "'ι₁'".
Reserved Notation "'ι₂'".
Reserved Notation "'π₁'".
Reserved Notation "'π₂'".

Reserved Notation "A × B" (at level 54, left associativity).
Reserved Notation "A ⊗ B" (at level 54, left associativity).
Reserved Notation "A ⊕ B" (at level 50, left associativity).

Reserved Notation "A ⇒ B" (at level 35, right associativity).
Reserved Notation "A ⊸ B" (at level 35, right associativity).

Reserved Notation "F ▹ nt" (at level 36).
Reserved Notation "nt ◃ F" (at level 36).

Reserved Notation "‖ x ‖" (at level 20, format "‖ x ‖").
Reserved Notation "a ♯ b" (at level 25, no associativity, format "a ♯ b").
Reserved Notation "u ⇋ v" (at level 20, no associativity).
Reserved Notation "p · x" (at level 35, right associativity, format "p · x").
Reserved Notation "'ν' x , t" (at level 50, format "'ν'  x ,  t").
