Load monoidal_category.

Load finite_types.

Definition BSym_cat : PreCategory.
Proof.
  apply (Build_PreCategory (fun a b : nat => fintype a <~> fintype b)).
  srapply @Build_PreCategory.
  - exact nat.
  - 

Definition BSym : Symmetric_Monoidal_Category.
Proof.
  
srapply @Build_Symmetric_Monoidal_Category.