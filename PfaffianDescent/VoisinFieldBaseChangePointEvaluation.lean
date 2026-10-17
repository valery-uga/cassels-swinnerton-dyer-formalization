import PfaffianDescent.VoisinFieldBaseChangeOpen
import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

/-!
# Evaluating base-changed functions at field-valued points

This connects the affine open base-change equivalence to the field-point
evaluation maps used in the fixed-linear-system descent endpoint.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/-- A ground-field constant evaluates at a compatible field-valued point
through the specified field extension. -/
theorem fieldPointΓevaluation_affineFunctionHom
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (c : K) :
    fieldPointΓevaluation x (affineFunctionHom base c) = algebraMap K L c := by
  have h := fieldPointΓevaluation_comp x base
    ((Scheme.ΓSpecIso (.of K)).inv.hom c)
  change fieldPointΓevaluation (x ≫ base)
      ((Scheme.ΓSpecIso (.of K)).inv.hom c) =
    fieldPointΓevaluation x (affineFunctionHom base c) at h
  rw [← h, hx]
  exact fieldPointΓevaluation_Spec_map (algebraMap K L) c

/-- The same formula on the top open of a scheme. -/
theorem fieldPointΓevaluation_schemeOpenBaseRingHom_top
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (c : K) :
    fieldPointΓevaluation x (schemeOpenBaseRingHom base ⊤ c) =
      algebraMap K L c := by
  rw [schemeOpenBaseRingHom_top_apply]
  exact fieldPointΓevaluation_affineFunctionHom base x hx c

/-- A function constant from the coefficient field evaluates to that same
coefficient at any field-valued point over the identity base map. -/
theorem fieldPointΓevaluation_schemeOpenBaseRingHom_top_over_id
    {L : Type u} [Field L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of L))
    (x : Spec (.of L) ⟶ X) (hx : x ≫ base = 𝟙 _)
    (c : L) :
    fieldPointΓevaluation x (schemeOpenBaseRingHom base ⊤ c) = c := by
  have h := fieldPointΓevaluation_comp x base
    ((Scheme.ΓSpecIso (.of L)).inv.hom c)
  change fieldPointΓevaluation (x ≫ base)
      ((Scheme.ΓSpecIso (.of L)).inv.hom c) =
    fieldPointΓevaluation x (affineFunctionHom base c) at h
  rw [schemeOpenBaseRingHom_top_apply, ← h, hx,
    fieldPointΓevaluation_id]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (.of L)).inv_hom_id c

/-- Evaluating the base-changed function on an inverse-image affine open
gives the scalar times the evaluation of its original function at the
underlying point. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (c : L) (r : Γ((U : Scheme.{u}), ⊤)) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pU ⊤)
    ∀ (xV : Spec (.of L) ⟶ (V : Scheme.{u}))
      (hxV : xV ≫ pV = 𝟙 _)
      (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
      (hmap : xV ≫ (g ∣_ U) = xU),
      fieldPointΓevaluation xV
        (schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U
          (c ⊗ₜ[K] r)) =
        c * fieldPointΓevaluation xU r := by
  dsimp only
  intro xV hxV xU hmap
  rw [schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv_tmul]
  rw [map_mul]
  rw [fieldPointΓevaluation_schemeOpenBaseRingHom_top_over_id
    _ xV hxV c]
  have heval := fieldPointΓevaluation_comp xV
    (schemeFieldBaseChangeToOriginal (L := L) base ∣_ U) r
  rw [hmap] at heval
  rw [← heval]

/-- Field-point evaluation is linear over the ground field when the point
lies over the specified field extension. -/
noncomputable def fieldPointΓevaluationLinearMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom base ⊤)
    Γ(X, ⊤) →ₗ[K] L := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom base ⊤)
  exact {
    toFun := fieldPointΓevaluation x
    map_add' := fun a b => map_add (fieldPointΓevaluation x) a b
    map_smul' := by
      intro c a
      simp only [RingHom.id_apply]
      change fieldPointΓevaluation x
          ((schemeOpenBaseRingHom base ⊤ c) • a) =
        c • fieldPointΓevaluation x a
      rw [smul_eq_mul, Algebra.smul_def, map_mul,
        fieldPointΓevaluation_schemeOpenBaseRingHom_top base x hx c]
  }

@[simp]
theorem fieldPointΓevaluationLinearMap_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : Γ(X, ⊤)) :
    fieldPointΓevaluationLinearMap base x hx a =
      fieldPointΓevaluation x a := rfl

/-- The pure-tensor formula extends to all scalar-extended regular functions.
This is the affine-coordinate evaluation naturality used in the geometric
base-change endpoint. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) [IsAffine (U : Scheme.{u})] :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pU ⊤)
    ∀ (xV : Spec (.of L) ⟶ (V : Scheme.{u}))
      (hxV : xV ≫ pV = 𝟙 _)
      (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
      (hmap : xV ≫ (g ∣_ U) = xU)
      (hxU : xU ≫ pU =
        Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (w : L ⊗[K] Γ((U : Scheme.{u}), ⊤)),
      fieldPointΓevaluation xV
        (schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U w) =
      LinearMap.liftBaseChange L
        (fieldPointΓevaluationLinearMap pU xU hxU) w := by
  dsimp only
  intro xV hxV xU hmap hxU w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul c r =>
      rw [fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul
        base U c r xV hxV xU hmap,
        LinearMap.liftBaseChange_tmul]
      simp only [fieldPointΓevaluationLinearMap_apply]
      rfl

/-- On a free affine chart, each coordinate of a pulled-back module section
has the same field-point evaluation as the scalar extension of its original
coordinate. This combines free-module base change with function evaluation. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenFreeModuleSections_tmul_coord
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    let eU := BundleSectionZeroLocus.localFreeIsoOfOver U I t ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V
    ∀ (xV : Spec (.of L) ⟶ (V : Scheme.{u}))
      (hxV : xV ≫ pV = 𝟙 _)
      (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
      (hmap : xV ≫ (g ∣_ U) = xU)
      (c : L) (s : SchemeModuleOpenSectionsOver base M U) (i : I),
      fieldPointΓevaluation xV
        (moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV
          (qV.symm (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
            base M U I t (c ⊗ₜ[K] s))) i) =
        c * fieldPointΓevaluation xU
          (moduleOpenTopLinearEquivOfFreeIsoOver pU I (M.restrict U.ι) eU
            (qU.symm s) i) := by
  dsimp only
  intro xV hxV xU hmap c s i
  rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_coord]
  exact fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul
    base U c _ xV hxV xU hmap

/-- Canonical lift of a field-valued point on an open to the corresponding
inverse-image open in the field base change. -/
noncomputable def schemeFieldBaseChangeOpenPoint
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Spec (.of L) ⟶
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U : Scheme.{u}) :=
  (isPullback_schemeFieldBaseChangeOpen base U).lift xU (𝟙 _)
    (by simpa using hxU)

@[reassoc (attr := simp)]
theorem schemeFieldBaseChangeOpenPoint_toOriginal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    schemeFieldBaseChangeOpenPoint base U xU hxU ≫
      (schemeFieldBaseChangeToOriginal (L := L) base ∣_ U) = xU :=
  (isPullback_schemeFieldBaseChangeOpen base U).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem schemeFieldBaseChangeOpenPoint_toField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    schemeFieldBaseChangeOpenPoint base U xU hxU ≫
      ((schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U).ι ≫
        schemeFieldBaseChangeToField (L := L) base) = 𝟙 _ :=
  (isPullback_schemeFieldBaseChangeOpen base U).lift_snd _ _ _

/-- The field-point evaluation formula with the canonical lifted point;
no separate compatibility datum for the lift is required. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul_canonical
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (c : L) (r : Γ((U : Scheme.{u}), ⊤)) :
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom (U.ι ≫ base) ⊤)
    fieldPointΓevaluation
        (schemeFieldBaseChangeOpenPoint base U xU hxU)
        (schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U
          (c ⊗ₜ[K] r)) =
      c * fieldPointΓevaluation xU r := by
  dsimp only
  exact fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul
    base U c r
      (schemeFieldBaseChangeOpenPoint base U xU hxU)
      (schemeFieldBaseChangeOpenPoint_toField base U xU hxU)
      xU (schemeFieldBaseChangeOpenPoint_toOriginal base U xU hxU)

/-- Free-module coordinate evaluation after field base change at the
canonical lifted point. The only point datum is the original field-valued
point on the trivializing open. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenFreeModuleSections_tmul_coord_canonical
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (c : L) (s : SchemeModuleOpenSectionsOver base M U) (i : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    let eU := BundleSectionZeroLocus.localFreeIsoOfOver U I t ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V
    fieldPointΓevaluation
        (schemeFieldBaseChangeOpenPoint base U xU hxU)
        (moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV
          (qV.symm (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
            base M U I t (c ⊗ₜ[K] s))) i) =
      c * fieldPointΓevaluation xU
        (moduleOpenTopLinearEquivOfFreeIsoOver pU I (M.restrict U.ι) eU
          (qU.symm s) i) := by
  dsimp only
  rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_coord]
  exact fieldPointΓevaluation_schemeFieldBaseChangeOpenGlobalFunctions_tmul_canonical
    base U xU hxU c _

end

end PfaffianDescent
