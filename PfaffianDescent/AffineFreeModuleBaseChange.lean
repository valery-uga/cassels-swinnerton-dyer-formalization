import PfaffianDescent.SchemeModuleCoverEqualizer
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.VoisinGlobalSectionsBaseChange
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Free module sections on affine schemes and scalar extension

This file packages two algebraic identifications used in the affine-chart
part of Voisin's global-section base-change argument.  On an affine spectrum,
the sections of a free module sheaf are the corresponding finitely supported
free module.  Scalar extension commutes with that finitely supported free
module construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

noncomputable section

private theorem freeModuleOpenTop_eval_zero
    {X : Scheme.{u}} (I : Type u) :
    (((0 : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) I).val.app (op ⊤)).hom) = 0 := by
  rfl

private theorem freeModuleOpenTop_eval_add
    {X : Scheme.{u}} (I : Type u)
    (f g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) I) :
    (((f + g).val.app (op ⊤)).hom) =
      (f.val.app (op ⊤)).hom + (g.val.app (op ⊤)).hom := by
  rfl

/-- Sections over the top open of a finite-rank free module sheaf are finite
tuples of global regular functions.  This coordinate equivalence is valid on
an arbitrary scheme; affineness is only needed later to identify the
coordinate ring after field base change. -/
noncomputable def freeModuleOpenTopLinearEquiv
    {X : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I] :
    Γ((show X.Modules from
      SheafOfModules.free (R := X.ringCatSheaf) I), ⊤) ≃ₗ[Γ(X, ⊤)]
      (I → Γ(X, ⊤)) where
  toFun s i :=
    ((BundleSectionZeroLocus.freeCoordinateMap (X := X) I i).val.app
      (op ⊤)).hom s
  invFun v := ∑ i : I,
    ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app
      (op ⊤)).hom (v i)
  left_inv s := by
    let F := fun i : I ↦
      BundleSectionZeroLocus.freeCoordinateMap (X := X) I i ≫
        SheafOfModules.ιFree i
    have hsum (t : Finset I) :
        (((∑ i ∈ t, F i).val.app (op ⊤)).hom s) =
          ∑ i ∈ t,
            ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app
              (op ⊤)).hom
              (((BundleSectionZeroLocus.freeCoordinateMap
                (X := X) I i).val.app (op ⊤)).hom s) := by
      induction t using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          have hz := congrArg (fun q => q s)
            (freeModuleOpenTop_eval_zero (X := X) I)
          exact hz.trans (LinearMap.zero_apply _)
      | @insert a t ha ih =>
          simp only [Finset.sum_insert, ha, not_false_eq_true]
          have hadd := congrArg (fun q => q s)
            (freeModuleOpenTop_eval_add
              (X := X) I (F a) (∑ i ∈ t, F i))
          calc
            (((F a + ∑ i ∈ t, F i).val.app (op ⊤)).hom s) =
                ((((F a).val.app (op ⊤)).hom +
                  ((∑ i ∈ t, F i).val.app (op ⊤)).hom) s) := hadd
            _ = (((F a).val.app (op ⊤)).hom s) +
                (((∑ i ∈ t, F i).val.app (op ⊤)).hom s) :=
              LinearMap.add_apply _ _ _
            _ = ((SheafOfModules.ιFree
                    (R := X.ringCatSheaf) a).val.app (op ⊤)).hom
                  (((BundleSectionZeroLocus.freeCoordinateMap
                    (X := X) I a).val.app (op ⊤)).hom s) +
                ∑ i ∈ t,
                  ((SheafOfModules.ιFree
                    (R := X.ringCatSheaf) i).val.app (op ⊤)).hom
                    (((BundleSectionZeroLocus.freeCoordinateMap
                      (X := X) I i).val.app (op ⊤)).hom s) := by
              rw [ih]
              rfl
    have h := congrArg
      (fun q : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
          SheafOfModules.free (R := X.ringCatSheaf) I ↦
        (q.val.app (op ⊤)).hom s)
      (BundleSectionZeroLocus.coordinateExpansion_eq_id (X := X) I)
    have hid :
        (((BundleSectionZeroLocus.coordinateExpansion
          (X := X) I).val.app (op ⊤)).hom s) = s := by
      have h' := h
      simp only [SheafOfModules.id_val, PresheafOfModules.id_app,
        ModuleCat.hom_id] at h'
      exact h'.trans rfl
    rw [BundleSectionZeroLocus.coordinateExpansion] at hid
    exact (hsum Finset.univ).symm.trans hid
  right_inv v := by
    funext j
    let p := ((BundleSectionZeroLocus.freeCoordinateMap
      (X := X) I j).val.app (op ⊤)).hom
    change p (∑ i : I,
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app
        (op ⊤)).hom (v i)) = v j
    rw [map_sum]
    rw [Finset.sum_eq_single j]
    · have h := congrArg
        (fun q : SheafOfModules.unit X.ringCatSheaf ⟶
            SheafOfModules.unit X.ringCatSheaf ↦
          (q.val.app (op ⊤)).hom (v j))
        (BundleSectionZeroLocus.iota_comp_freeCoordinateMap
          (X := X) I j j)
      have h1 :
          p (((SheafOfModules.ιFree
            (R := X.ringCatSheaf) j).val.app (op ⊤)).hom (v j)) =
            (((if j = j then 𝟙 (SheafOfModules.unit X.ringCatSheaf)
              else 0).val.app (op ⊤)).hom (v j)) := by
        exact h
      have h2 :
          (((if j = j then 𝟙 (SheafOfModules.unit X.ringCatSheaf)
              else 0).val.app (op ⊤)).hom (v j)) = v j := by
        rw [if_pos rfl]
        exact ModuleCat.id_apply
          ((SheafOfModules.unit X.ringCatSheaf).val.obj (op ⊤)) (v j)
      exact h1.trans h2
    · intro i _ hij
      have h := congrArg
        (fun q : SheafOfModules.unit X.ringCatSheaf ⟶
            SheafOfModules.unit X.ringCatSheaf ↦
          (q.val.app (op ⊤)).hom (v i))
        (BundleSectionZeroLocus.iota_comp_freeCoordinateMap
          (X := X) I j i)
      rw [if_neg hij] at h
      calc
        p (((SheafOfModules.ιFree
          (R := X.ringCatSheaf) i).val.app (op ⊤)).hom (v i)) =
            (p.comp ((SheafOfModules.ιFree
              (R := X.ringCatSheaf) i).val.app (op ⊤)).hom) (v i) := rfl
        _ = (((0 : SheafOfModules.unit X.ringCatSheaf ⟶
              SheafOfModules.unit X.ringCatSheaf).val.app
                (op ⊤)).hom (v i)) := h
        _ = 0 := by
          have hz := congrArg (fun q => q (v i))
            (show (((0 : SheafOfModules.unit X.ringCatSheaf ⟶
              SheafOfModules.unit X.ringCatSheaf).val.app
                (op ⊤)).hom) = 0 from rfl)
          exact hz.trans (LinearMap.zero_apply _)
    · simp
  map_add' s t := by
    funext i
    exact map_add _ _ _
  map_smul' r s := by
    funext i
    exact ((BundleSectionZeroLocus.freeCoordinateMap
      (X := X) I i).val.app (op ⊤)).hom.map_smul r s

/-- An isomorphism of module sheaves on one scheme induces the corresponding
linear equivalence on sections over the top open. -/
noncomputable def moduleOpenTopLinearEquivOfIso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤) where
  toFun := (e.hom.val.app (op ⊤)).hom
  invFun := (e.inv.val.app (op ⊤)).hom
  left_inv s := by
    have h := congrArg
      (fun q : M ⟶ M ↦ (q.val.app (op ⊤)).hom s)
      e.hom_inv_id
    have h1 : (e.inv.val.app (op ⊤)).hom
        ((e.hom.val.app (op ⊤)).hom s) =
        ((((show M ⟶ M from 𝟙 M).val.app (op ⊤)).hom s)) := by
      exact h
    exact h1.trans (ModuleCat.id_apply _ _)
  right_inv s := by
    have h := congrArg
      (fun q : N ⟶ N ↦ (q.val.app (op ⊤)).hom s)
      e.inv_hom_id
    have h1 : (e.hom.val.app (op ⊤)).hom
        ((e.inv.val.app (op ⊤)).hom s) =
        ((((show N ⟶ N from 𝟙 N).val.app (op ⊤)).hom s)) := by
      exact h
    exact h1.trans (ModuleCat.id_apply _ _)
  map_add' s t := map_add _ _ _
  map_smul' r s := (e.hom.val.app (op ⊤)).hom.map_smul r s

/-- A finite free trivialization gives coordinates on the module's sections
over the top open. -/
noncomputable def moduleOpenTopLinearEquivOfFreeIso
    {X : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (M : X.Modules)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] (I → Γ(X, ⊤)) :=
  (moduleOpenTopLinearEquivOfIso e).symm ≪≫ₗ
    freeModuleOpenTopLinearEquiv I

/-- Free coordinates on top-open sections, regarded as coordinates over a
chosen ground field through the scheme's structure morphism. -/
noncomputable def moduleOpenTopLinearEquivOfFreeIsoOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (I : Type u) [Fintype I] [DecidableEq I]
    (M : X.Modules)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    SchemeModuleOpenSectionsOver p M ⊤ ≃ₗ[K] (I → Γ(X, ⊤)) := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  let q := moduleOpenTopLinearEquivOfFreeIso I M e
  exact
    { __ := q
      map_smul' c s := q.map_smul (schemeOpenBaseRingHom p ⊤ c) s }

/-- For finite free module sheaves, base change of top-open sections reduces
functorially to base change of the two rings of global functions.  This is
the local module theorem needed on each affine chart and pairwise overlap in
the Cech assembly. -/
noncomputable def freeModuleOpenSectionsBaseChangeLinearEquivOfRing
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (pL : Y ⟶ Spec (.of L))
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : X.Modules) (ML : Y.Modules)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (eL : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ ML)
    (ringEquiv :
      letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
      letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pL ⊤)
      (L ⊗[K] Γ(X, ⊤)) ≃ₗ[L] Γ(Y, ⊤)) :
    (L ⊗[K] SchemeModuleOpenSectionsOver p M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver pL ML ⊤ := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pL ⊤)
  exact
    (moduleOpenTopLinearEquivOfFreeIsoOver p I M e).baseChange K L _ _ ≪≫ₗ
      tensorFinitePiLinearEquivOfFamily
        (fun _ : I ↦ Γ(X, ⊤)) (fun _ : I ↦ Γ(Y, ⊤))
        (fun _ ↦ ringEquiv) ≪≫ₗ
      (moduleOpenTopLinearEquivOfFreeIsoOver pL I ML eL).symm

/-- In free coordinates, the finite-free section base-change equivalence is
the supplied ring base-change equivalence in every coordinate. -/
theorem freeModuleOpenSectionsBaseChangeLinearEquivOfRing_tmul_coord
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (pL : Y ⟶ Spec (.of L))
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : X.Modules) (ML : Y.Modules)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (eL : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ ML)
    (ringEquiv :
      letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
      letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pL ⊤)
      (L ⊗[K] Γ(X, ⊤)) ≃ₗ[L] Γ(Y, ⊤))
    (c : L) (s : SchemeModuleOpenSectionsOver p M ⊤) (i : I) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pL ⊤)
    moduleOpenTopLinearEquivOfFreeIsoOver pL I ML eL
        (freeModuleOpenSectionsBaseChangeLinearEquivOfRing
          p pL I M ML e eL ringEquiv (c ⊗ₜ[K] s)) i =
      ringEquiv (c ⊗ₜ[K]
        moduleOpenTopLinearEquivOfFreeIsoOver p I M e s i) := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pL ⊤)
  simp [freeModuleOpenSectionsBaseChangeLinearEquivOfRing]

/-- Under the standard affine identification, the functions supplied by a
map `Spec A → Spec K` are exactly the given algebra map `K → A`. -/
theorem gammaSpec_baseRingHom_apply
    {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
    (c : K) :
    (Scheme.ΓSpecIso (.of A)).hom.hom
      (affineFunctionHom
        (Spec.map (CommRingCat.ofHom (algebraMap K A))) c) =
      algebraMap K A c := by
  unfold affineFunctionHom
  change (Scheme.ΓSpecIso (.of A)).hom.hom
    (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop).hom c) = _
  rw [← CommRingCat.comp_apply, Category.assoc,
    Scheme.ΓSpecIso_naturality]
  simp

/-- The canonical affine identification `Γ(Spec A, O) ≃ A`, made linear
over a field acting through the structural morphism `Spec A → Spec K`. -/
noncomputable def specGlobalFunctionsLinearEquiv
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    Γ(Spec (.of A), ⊤) ≃ₗ[K] A := by
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  exact
    { __ := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
      map_smul' c s := by
        have hs : c • s = schemeOpenBaseRingHom p ⊤ c * s := by rfl
        rw [hs]
        simp only [RingHom.id_apply, Algebra.smul_def]
        change (Scheme.ΓSpecIso (.of A)).hom.hom
          (schemeOpenBaseRingHom p ⊤ c * s) =
            algebraMap K A c * (Scheme.ΓSpecIso (.of A)).hom.hom s
        rw [map_mul, schemeOpenBaseRingHom_top_apply]
        congr 1
        exact gammaSpec_baseRingHom_apply c }

/-- Global functions on an affine spectrum commute with extension of the
ground field, on the standard affine model of the fiber product. -/
noncomputable def specGlobalFunctionsBaseChangeLinearEquiv
    (K L A : Type u) [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    let pL : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of L) :=
      Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    letI := Module.compHom Γ(Spec (.of (L ⊗[K] A)), ⊤)
      (schemeOpenBaseRingHom pL ⊤)
    (L ⊗[K] Γ(Spec (.of A), ⊤)) ≃ₗ[L]
      Γ(Spec (.of (L ⊗[K] A)), ⊤) := by
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  let pL : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(Spec (.of (L ⊗[K] A)), ⊤)
    (schemeOpenBaseRingHom pL ⊤)
  exact (specGlobalFunctionsLinearEquiv K A).baseChange K L _ _ ≪≫ₗ
    (specGlobalFunctionsLinearEquiv L (L ⊗[K] A)).symm

/-- The complete local affine theorem for a finite free module: sections of
the pulled-back module on `Spec (L ⊗[K] A)` are the scalar extension of its
sections on `Spec A`. -/
noncomputable def specFreeModuleOpenSectionsBaseChangeLinearEquiv
    (K L A : Type u) [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    let pL : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of L) :=
      Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))
    let f : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* L ⊗[K] A))
    (L ⊗[K] SchemeModuleOpenSectionsOver p M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver pL
        ((Scheme.Modules.pullback f).obj M) ⊤ := by
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  let pL : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))
  let f : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        A →+* L ⊗[K] A))
  let eL := BundleSectionZeroLocus.pullbackFreeIso f I e
  exact freeModuleOpenSectionsBaseChangeLinearEquivOfRing
    p pL I M ((Scheme.Modules.pullback f).obj M) e eL
      (specGlobalFunctionsBaseChangeLinearEquiv K L A)

/-- Global sections of the free sheaf on `Spec R`, with the canonical
`R`-module structure used by the affine `tilde` equivalence, are the
finitely supported free `R`-module on the same index type. -/
noncomputable def specFreeModuleSectionsLinearEquiv
    (R : Type u) [CommRing R] (I : Type u) :
    (I →₀ R) ≃ₗ[R]
      (moduleSpecΓFunctor (R := CommRingCat.of R)).obj
        (SheafOfModules.free
          (R := (Spec (.of R)).ringCatSheaf) I) :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app
      (ModuleCat.of R (I →₀ R)) ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of R)).mapIso
      (tildeFinsupp I)).toLinearEquiv

/-- A chosen free presentation of a module sheaf on `Spec R` identifies its
global sections with a finitely supported free module. -/
noncomputable def specModuleSectionsLinearEquivOfFreeIso
    (R : Type u) [CommRing R] (I : Type u)
    (M : (Spec (.of R)).Modules)
    (e : SheafOfModules.free
      (R := (Spec (.of R)).ringCatSheaf) I ≅ M) :
    (I →₀ R) ≃ₗ[R] (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M :=
  specFreeModuleSectionsLinearEquiv R I ≪≫ₗ
    ((moduleSpecΓFunctor (R := CommRingCat.of R)).mapIso e).toLinearEquiv

/-- Scalar extension commutes with finitely supported free modules.  The
second equivalence can, in applications, be the affine coordinate-ring
base-change equivalence. -/
noncomputable def tensorFinsuppLinearEquivOf
    {K L A B : Type u} [CommRing K] [CommRing L]
    [AddCommGroup A] [AddCommGroup B]
    [Algebra K L] [Module K A] [Module L B]
    (I : Type u) [DecidableEq I]
    (e : (L ⊗[K] A) ≃ₗ[L] B) :
    (L ⊗[K] (I →₀ A)) ≃ₗ[L] (I →₀ B) :=
  TensorProduct.finsuppRight K L L A I ≪≫ₗ
    Finsupp.mapRange.linearEquiv e

@[simp]
theorem tensorFinsuppLinearEquivOf_tmul_apply
    {K L A B : Type u} [CommRing K] [CommRing L]
    [AddCommGroup A] [AddCommGroup B]
    [Algebra K L] [Module K A] [Module L B]
    (I : Type u) [DecidableEq I]
    (e : (L ⊗[K] A) ≃ₗ[L] B)
    (c : L) (a : I →₀ A) (i : I) :
    tensorFinsuppLinearEquivOf I e (c ⊗ₜ[K] a) i =
      e (c ⊗ₜ[K] a i) := by
  simp [tensorFinsuppLinearEquivOf]

/-- On an affine spectrum, global sections of a finite free module commute
with extension of the ground field.  The target is written on the standard
affine model `Spec (L ⊗[K] A)` of the base-changed spectrum, and the module
is the pullback along the morphism induced by `A → L ⊗[K] A`.

The module structures displayed by `Module.compHom` are made explicit so
that this theorem can later be transported to the ground-field structures
coming from scheme structure morphisms. -/
noncomputable def affineFreeModuleSectionsBaseChangeLinearEquiv
    (K L A : Type u) [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A]
    (I : Type u) [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M) :
    letI := Module.compHom
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj M)
      (algebraMap K A)
    letI := Module.compHom
      ((moduleSpecΓFunctor (R := CommRingCat.of (L ⊗[K] A))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* L ⊗[K] A)))).obj M))
      (algebraMap L (L ⊗[K] A))
    (L ⊗[K] (moduleSpecΓFunctor (R := CommRingCat.of A)).obj M) ≃ₗ[L]
      (moduleSpecΓFunctor (R := CommRingCat.of (L ⊗[K] A))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* L ⊗[K] A)))).obj M) := by
  letI := Module.compHom
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj M)
    (algebraMap K A)
  letI : IsScalarTower K A
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : Spec (.of (L ⊗[K] A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* L ⊗[K] A))
  let eL := BundleSectionZeroLocus.pullbackFreeIso f I e
  letI := Module.compHom
    ((moduleSpecΓFunctor (R := CommRingCat.of (L ⊗[K] A))).obj
      ((Scheme.Modules.pullback f).obj M))
    (algebraMap L (L ⊗[K] A))
  letI : IsScalarTower L (L ⊗[K] A)
      ((moduleSpecΓFunctor (R := CommRingCat.of (L ⊗[K] A))).obj
        ((Scheme.Modules.pullback f).obj M)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let ground :=
    (specModuleSectionsLinearEquivOfFreeIso A I M e).symm.restrictScalars K
  let extended :=
    (specModuleSectionsLinearEquivOfFreeIso
      (L ⊗[K] A) I ((Scheme.Modules.pullback f).obj M) eL).restrictScalars L
  exact
    ground.baseChange K L _ _ ≪≫ₗ
      tensorFinsuppLinearEquivOf I
        (LinearEquiv.refl L (L ⊗[K] A)) ≪≫ₗ
      extended

end

end PfaffianDescent
