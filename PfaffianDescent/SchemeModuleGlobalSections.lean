import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.SchemeModuleTensor

namespace PfaffianDescent

open CategoryTheory AlgebraicGeometry BundleSectionZeroLocus

universe u

noncomputable section

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The structure sheaf regarded as an object of the category of
module sheaves.  Naming it fixes the universe of the ambient category. -/
noncomputable def schemeModuleUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Multiplication by a scalar from the ground field as an endomorphism of
`O_X`. -/
noncomputable def schemeModuleConstantEndomorphism
    (p : X ⟶ Spec (.of K)) (c : K) :
    schemeModuleUnit X ⟶ schemeModuleUnit X :=
  unitEndomorphismOfRegularFunction (affineFunctionHom p c)

/-- Constant scalar multiplication on the structure sheaf is additive in
the scalar. -/
noncomputable def schemeModuleConstantEndomorphismAddHom
    (p : X ⟶ Spec (.of K)) :
    K →+ (schemeModuleUnit X ⟶ schemeModuleUnit X) where
  toFun := schemeModuleConstantEndomorphism p
  map_zero' := by
    change unitEndomorphismOfRegularFunction (affineFunctionHom p 0) = 0
    rw [map_zero, unitEndomorphismOfRegularFunction_zero]
  map_add' a b := by
    change unitEndomorphismOfRegularFunction (affineFunctionHom p (a + b)) =
      unitEndomorphismOfRegularFunction (affineFunctionHom p a) +
        unitEndomorphismOfRegularFunction (affineFunctionHom p b)
    rw [map_add, unitEndomorphismOfRegularFunction_add]

/-- A global section of `M` on a `K`-scheme, represented by the corresponding
morphism `O_X ⟶ M`. -/
def SchemeModuleGlobalSectionsOver
    (_p : X ⟶ Spec (.of K)) (M : X.Modules) :=
  schemeModuleUnit X ⟶ M

noncomputable instance (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    AddCommGroup (SchemeModuleGlobalSectionsOver p M) :=
  inferInstanceAs (AddCommGroup (schemeModuleUnit X ⟶ M))

noncomputable instance (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    Module K (SchemeModuleGlobalSectionsOver p M) where
  smul c s := schemeModuleConstantEndomorphism p c ≫ s
  one_smul s := by
    change schemeModuleConstantEndomorphism p 1 ≫ s = s
    rw [schemeModuleConstantEndomorphism, map_one,
      unitEndomorphismOfRegularFunction_one]
    exact Category.id_comp s
  mul_smul c d s := by
    change schemeModuleConstantEndomorphism p (c * d) ≫ s =
      schemeModuleConstantEndomorphism p c ≫
        (schemeModuleConstantEndomorphism p d ≫ s)
    rw [schemeModuleConstantEndomorphism, map_mul,
      unitEndomorphismOfRegularFunction_mul]
    exact Category.assoc _ _ _
  smul_zero c := by
    change schemeModuleConstantEndomorphism p c ≫
      (0 : schemeModuleUnit X ⟶ M) = 0
    exact CategoryTheory.Limits.comp_zero
  smul_add c s t := by
    change schemeModuleConstantEndomorphism p c ≫ (s + t) =
      schemeModuleConstantEndomorphism p c ≫ s +
        schemeModuleConstantEndomorphism p c ≫ t
    exact Preadditive.comp_add _ _ _ _ _ _
  add_smul c d s := by
    change schemeModuleConstantEndomorphism p (c + d) ≫ s =
      schemeModuleConstantEndomorphism p c ≫ s +
        schemeModuleConstantEndomorphism p d ≫ s
    rw [schemeModuleConstantEndomorphism, map_add,
      unitEndomorphismOfRegularFunction_add]
    exact Preadditive.add_comp _ _ _ _ _ _
  zero_smul s := by
    change schemeModuleConstantEndomorphism p 0 ≫ s = 0
    rw [schemeModuleConstantEndomorphism, map_zero,
      unitEndomorphismOfRegularFunction_zero]
    exact CategoryTheory.Limits.zero_comp

/-- The morphism/compatible-family equivalence for global sections. -/
noncomputable def schemeModuleGlobalSectionsOverEquivSections
    (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    SchemeModuleGlobalSectionsOver p M ≃ M.sections :=
  M.unitHomEquiv

/-- A morphism of module sheaves induces a linear map on global sections. -/
noncomputable def schemeModuleGlobalSectionsMap
    (p : X ⟶ Spec (.of K)) {M N : X.Modules} (f : M ⟶ N) :
    SchemeModuleGlobalSectionsOver p M →ₗ[K]
      SchemeModuleGlobalSectionsOver p N where
  toFun s := s ≫ f
  map_add' s t := by
    change (s + t) ≫ f = s ≫ f + t ≫ f
    exact Preadditive.add_comp _ _ _ s t f
  map_smul' c s := by
    change (unitEndomorphismOfRegularFunction (affineFunctionHom p c) ≫ s) ≫ f =
      unitEndomorphismOfRegularFunction (affineFunctionHom p c) ≫ (s ≫ f)
    exact Category.assoc _ _ _

/-- Tensor product of two morphism-valued global sections. -/
noncomputable def schemeModuleTensorGlobalSection
    (p : X ⟶ Spec (.of K)) (M N : X.Modules)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    SchemeModuleGlobalSectionsOver p (schemeModuleTensor M N) :=
  (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
    schemeModuleTensorMap s t

/-- Transport the tensor product of two global sections through a supplied
isomorphism of module sheaves. -/
noncomputable def schemeModuleGlobalSectionProduct
    (p : X ⟶ Spec (.of K)) (M N P : X.Modules)
    (e : schemeModuleTensor M N ≅ P)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    SchemeModuleGlobalSectionsOver p P :=
  schemeModuleGlobalSectionsMap p e.hom
    (schemeModuleTensorGlobalSection p M N s t)

/-- The morphism-valued tensor product agrees with the compatible-family
construction `schemeModuleTensorSection`. -/
theorem schemeModuleTensorGlobalSection_toSections
    (p : X ⟶ Spec (.of K)) (M N : X.Modules)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleGlobalSectionsOverEquivSections p (schemeModuleTensor M N)
        (schemeModuleTensorGlobalSection p M N s t) =
      schemeModuleTensorSection M N
        (schemeModuleGlobalSectionsOverEquivSections p M s)
        (schemeModuleGlobalSectionsOverEquivSections p N t) := by
  unfold schemeModuleGlobalSectionsOverEquivSections
  unfold schemeModuleTensorGlobalSection schemeModuleTensorSection
  have hs : M.unitHomEquiv.symm (M.unitHomEquiv s) = s :=
    M.unitHomEquiv.symm_apply_apply s
  have ht : N.unitHomEquiv.symm (N.unitHomEquiv t) = t :=
    N.unitHomEquiv.symm_apply_apply t
  have hmap : schemeModuleTensorMap
        (M.unitHomEquiv.symm (M.unitHomEquiv s))
        (N.unitHomEquiv.symm (N.unitHomEquiv t)) =
      schemeModuleTensorMap s t :=
    congrArg₂ (fun a b => schemeModuleTensorMap a b) hs ht
  exact congrArg (fun q => (schemeModuleTensor M N).unitHomEquiv
    ((schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫ q)) hmap.symm

/-- Tensor product of global sections is additive in the first section. -/
theorem schemeModuleTensorGlobalSection_add_first
    (p : X ⟶ Spec (.of K)) (M N : X.Modules)
    (s₁ s₂ : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleTensorGlobalSection p M N (s₁ + s₂) t =
      schemeModuleTensorGlobalSection p M N s₁ t +
        schemeModuleTensorGlobalSection p M N s₂ t := by
  change (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
      schemeModuleTensorMap (s₁ + s₂) t =
    (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
        schemeModuleTensorMap s₁ t +
      (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
        schemeModuleTensorMap s₂ t
  have h : schemeModuleTensorMap (s₁ + s₂) t =
      schemeModuleTensorMap s₁ t + schemeModuleTensorMap s₂ t := by
    exact schemeModuleTensorMap_add_first s₁ s₂ t
  calc
    _ = (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
          (schemeModuleTensorMap s₁ t + schemeModuleTensorMap s₂ t) :=
      congrArg (fun q =>
        (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫ q) h
    _ = _ := Preadditive.comp_add _ _ _ _ _ _

/-- Tensor product of global sections is additive in the second section. -/
theorem schemeModuleTensorGlobalSection_add_second
    (p : X ⟶ Spec (.of K)) (M N : X.Modules)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t₁ t₂ : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleTensorGlobalSection p M N s (t₁ + t₂) =
      schemeModuleTensorGlobalSection p M N s t₁ +
        schemeModuleTensorGlobalSection p M N s t₂ := by
  change (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
      schemeModuleTensorMap s (t₁ + t₂) =
    (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
        schemeModuleTensorMap s t₁ +
      (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
        schemeModuleTensorMap s t₂
  have h : schemeModuleTensorMap s (t₁ + t₂) =
      schemeModuleTensorMap s t₁ + schemeModuleTensorMap s t₂ := by
    exact schemeModuleTensorMap_add_second s t₁ t₂
  calc
    _ = (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫
          (schemeModuleTensorMap s t₁ + schemeModuleTensorMap s t₂) :=
      congrArg (fun q =>
        (schemeModuleTensorUnitLeftIso (schemeModuleUnit X)).inv ≫ q) h
    _ = _ := Preadditive.comp_add _ _ _ _ _ _

/-- Tensor product of global sections is linear in the first section. -/
theorem schemeModuleTensorGlobalSection_smul_first
    (p : X ⟶ Spec (.of K)) (M N : X.Modules) (c : K)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleTensorGlobalSection p M N (c • s) t =
      c • schemeModuleTensorGlobalSection p M N s t := by
  let O := schemeModuleUnit X
  let a : O ⟶ O := schemeModuleConstantEndomorphism p c
  let unitInv := (schemeModuleTensorUnitLeftIso O).inv
  have hcomp : schemeModuleTensorMap (a ≫ s) t =
      schemeModuleTensorMap a (𝟙 O) ≫ schemeModuleTensorMap s t := by
    have h := schemeModuleTensorMap_comp a (𝟙 O) s t
    have ht : (𝟙 O) ≫ t = t := Category.id_comp t
    exact (congrArg (fun q => schemeModuleTensorMap (a ≫ s) q) ht.symm).trans h.symm
  have hcentral : schemeModuleTensorMap a (𝟙 O) =
      schemeModuleTensorMap (𝟙 O) a := by
    exact schemeModuleTensorMap_unit_central a
  have hunit : unitInv ≫ schemeModuleTensorMap (𝟙 O) a = a ≫ unitInv := by
    exact schemeModuleTensorUnitLeftIso_inv_naturality a
  change unitInv ≫ schemeModuleTensorMap (a ≫ s) t =
    a ≫ (unitInv ≫ schemeModuleTensorMap s t)
  calc
    unitInv ≫ schemeModuleTensorMap (a ≫ s) t =
        unitInv ≫ (schemeModuleTensorMap a (𝟙 O) ≫
          schemeModuleTensorMap s t) := congrArg (fun q => unitInv ≫ q) hcomp
    _ = (unitInv ≫ schemeModuleTensorMap a (𝟙 O)) ≫
        schemeModuleTensorMap s t := (Category.assoc _ _ _).symm
    _ = (unitInv ≫ schemeModuleTensorMap (𝟙 O) a) ≫
        schemeModuleTensorMap s t :=
      congrArg (fun q => (unitInv ≫ q) ≫ schemeModuleTensorMap s t) hcentral
    _ = (a ≫ unitInv) ≫ schemeModuleTensorMap s t :=
      congrArg (fun q => q ≫ schemeModuleTensorMap s t) hunit
    _ = a ≫ (unitInv ≫ schemeModuleTensorMap s t) := Category.assoc _ _ _

/-- Tensor product of global sections is linear in the second section. -/
theorem schemeModuleTensorGlobalSection_smul_second
    (p : X ⟶ Spec (.of K)) (M N : X.Modules) (c : K)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleTensorGlobalSection p M N s (c • t) =
      c • schemeModuleTensorGlobalSection p M N s t := by
  let O := schemeModuleUnit X
  let a : O ⟶ O := schemeModuleConstantEndomorphism p c
  let unitInv := (schemeModuleTensorUnitLeftIso O).inv
  have hcomp : schemeModuleTensorMap s (a ≫ t) =
      schemeModuleTensorMap (𝟙 O) a ≫ schemeModuleTensorMap s t := by
    have h := schemeModuleTensorMap_comp (𝟙 O) a s t
    have hs : (𝟙 O) ≫ s = s := Category.id_comp s
    exact (congrArg (fun q => schemeModuleTensorMap q (a ≫ t)) hs.symm).trans h.symm
  have hunit : unitInv ≫ schemeModuleTensorMap (𝟙 O) a = a ≫ unitInv := by
    exact schemeModuleTensorUnitLeftIso_inv_naturality a
  change unitInv ≫ schemeModuleTensorMap s (a ≫ t) =
    a ≫ (unitInv ≫ schemeModuleTensorMap s t)
  calc
    unitInv ≫ schemeModuleTensorMap s (a ≫ t) =
        unitInv ≫ (schemeModuleTensorMap (𝟙 O) a ≫
          schemeModuleTensorMap s t) := congrArg (fun q => unitInv ≫ q) hcomp
    _ = (unitInv ≫ schemeModuleTensorMap (𝟙 O) a) ≫
        schemeModuleTensorMap s t := (Category.assoc _ _ _).symm
    _ = (a ≫ unitInv) ≫ schemeModuleTensorMap s t :=
      congrArg (fun q => q ≫ schemeModuleTensorMap s t) hunit
    _ = a ≫ (unitInv ≫ schemeModuleTensorMap s t) := Category.assoc _ _ _

/-- Genuine multiplication of global sections as a bilinear map over the
base field. -/
noncomputable def schemeModuleGlobalSectionProductLinearMap
    (p : X ⟶ Spec (.of K)) (M N P : X.Modules)
    (e : schemeModuleTensor M N ≅ P) :
    SchemeModuleGlobalSectionsOver p M →ₗ[K]
      SchemeModuleGlobalSectionsOver p N →ₗ[K]
        SchemeModuleGlobalSectionsOver p P where
  toFun s :=
    { toFun := fun t => schemeModuleGlobalSectionProduct p M N P e s t
      map_add' := by
        intro t₁ t₂
        unfold schemeModuleGlobalSectionProduct
        have h := schemeModuleTensorGlobalSection_add_second p M N s t₁ t₂
        calc
          schemeModuleGlobalSectionsMap p e.hom
              (schemeModuleTensorGlobalSection p M N s (t₁ + t₂)) =
              schemeModuleGlobalSectionsMap p e.hom
                (schemeModuleTensorGlobalSection p M N s t₁ +
                  schemeModuleTensorGlobalSection p M N s t₂) :=
            congrArg (schemeModuleGlobalSectionsMap p e.hom) h
          _ = _ := (schemeModuleGlobalSectionsMap p e.hom).map_add _ _
      map_smul' := by
        intro c t
        unfold schemeModuleGlobalSectionProduct
        have h := schemeModuleTensorGlobalSection_smul_second p M N c s t
        calc
          schemeModuleGlobalSectionsMap p e.hom
              (schemeModuleTensorGlobalSection p M N s (c • t)) =
              schemeModuleGlobalSectionsMap p e.hom
                (c • schemeModuleTensorGlobalSection p M N s t) :=
            congrArg (schemeModuleGlobalSectionsMap p e.hom) h
          _ = _ := (schemeModuleGlobalSectionsMap p e.hom).map_smul c _ }
  map_add' := by
    intro s₁ s₂
    ext t
    change schemeModuleGlobalSectionProduct p M N P e (s₁ + s₂) t =
      schemeModuleGlobalSectionProduct p M N P e s₁ t +
        schemeModuleGlobalSectionProduct p M N P e s₂ t
    unfold schemeModuleGlobalSectionProduct
    have h := schemeModuleTensorGlobalSection_add_first p M N s₁ s₂ t
    calc
      schemeModuleGlobalSectionsMap p e.hom
          (schemeModuleTensorGlobalSection p M N (s₁ + s₂) t) =
          schemeModuleGlobalSectionsMap p e.hom
            (schemeModuleTensorGlobalSection p M N s₁ t +
              schemeModuleTensorGlobalSection p M N s₂ t) :=
        congrArg (schemeModuleGlobalSectionsMap p e.hom) h
      _ = _ := (schemeModuleGlobalSectionsMap p e.hom).map_add _ _
  map_smul' := by
    intro c s
    ext t
    change schemeModuleGlobalSectionProduct p M N P e (c • s) t =
      c • schemeModuleGlobalSectionProduct p M N P e s t
    unfold schemeModuleGlobalSectionProduct
    have h := schemeModuleTensorGlobalSection_smul_first p M N c s t
    calc
      schemeModuleGlobalSectionsMap p e.hom
          (schemeModuleTensorGlobalSection p M N (c • s) t) =
          schemeModuleGlobalSectionsMap p e.hom
            (c • schemeModuleTensorGlobalSection p M N s t) :=
        congrArg (schemeModuleGlobalSectionsMap p e.hom) h
      _ = _ := (schemeModuleGlobalSectionsMap p e.hom).map_smul c _

@[simp]
theorem schemeModuleGlobalSectionProductLinearMap_apply
    (p : X ⟶ Spec (.of K)) (M N P : X.Modules)
    (e : schemeModuleTensor M N ≅ P)
    (s : SchemeModuleGlobalSectionsOver p M)
    (t : SchemeModuleGlobalSectionsOver p N) :
    schemeModuleGlobalSectionProductLinearMap p M N P e s t =
      schemeModuleGlobalSectionProduct p M N P e s t := rfl

@[simp]
theorem schemeModuleGlobalSectionsMap_apply
    (p : X ⟶ Spec (.of K)) {M N : X.Modules} (f : M ⟶ N)
    (s : SchemeModuleGlobalSectionsOver p M) :
    schemeModuleGlobalSectionsMap p f s = s ≫ f := rfl

end

end PfaffianDescent
