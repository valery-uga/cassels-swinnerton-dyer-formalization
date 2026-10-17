import PfaffianDescent.CorayActualPositiveOpenFrameNormalizedEntries
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! Canonical positive-chart matrix coefficients by actual unit-Hom top1.
No frame conjugation certificate or replaced scalar action is a premise.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma inverseFrame_transfer
    {A B C D : AddCommGrpCat} (ea : A ≅ C) (eb : B ≅ C) (t : C ≅ D)
    (f : A ⟶ B) (g : D ⟶ D)
    (h : ∀ r : D, f ((ea ≪≫ t).inv r) = (eb ≪≫ t).inv (g r)) (q : C) :
    f (ea.inv q) = eb.inv (t.inv (g (t.hom q))) := by
  have ht : t.inv (t.hom q) = q :=
    ConcreteCategory.congr_hom t.hom_inv_id q
  calc
    f (ea.inv q) = f (ea.inv (t.inv (t.hom q))) :=
      congrArg (fun z => f (ea.inv z)) ht.symm
    _ = eb.inv (t.inv (g (t.hom q))) := h (t.hom q)

/-- Transfer the already-derived structure-section formula through the
ACTUAL top-open ring isomorphism. This cut has only ordinary AddGrp maps. -/
private lemma actualPositiveWeightedMultiplication_unitSectionsFrame
    (j : Fin 4) {d : ℕ} (p : PolyA) (hp : p.IsHomogeneous d)
    (a b : ℕ) (h : a + d = b) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (q : Γ((U : Scheme), ⊤)) :
    (actualPositiveWeightedMultiplication p hp a b h).val.app (op U)
        ((p3PositiveTwistSectionsIsoUnit K U j hU a).inv q) =
      (p3PositiveTwistSectionsIsoUnit K U j hU b).inv
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p) * q) := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let ea := p3PositiveTwistSectionsIsoUnit K U j hU a
  let eb := p3PositiveTwistSectionsIsoUnit K U j hU b
  let t := F.mapIso U.topIso
  let f := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (actualPositiveWeightedMultiplication p hp a b h)).app (op U)
  let c := actualAmbientChartCoefficientSection j U hU p
  let g : F.obj Γ(Proj PS, U) ⟶ F.obj Γ(Proj PS, U) := AddCommGrpCat.ofHom
    { toFun := fun r => c * r
      map_zero' := mul_zero c
      map_add' := fun r s => mul_add c r s }
  have hf : ∀ r : F.obj Γ(Proj PS, U),
      f ((ea ≪≫ t).inv r) = (eb ≪≫ t).inv (g r) :=
    actualPositiveWeightedMultiplication_structureFrame j p hp a b h U hU
  have hs := inverseFrame_transfer ea eb t f g hf q
  have hmul : t.inv (g (t.hom q)) = U.topIso.inv.hom c * q := by
    change U.topIso.inv.hom (c * U.topIso.hom.hom q) = _
    rw [map_mul]
    have ht : U.topIso.inv.hom (U.topIso.hom.hom q) = q :=
      ConcreteCategory.congr_hom U.topIso.hom_inv_id q
    exact congrArg (fun z => U.topIso.inv.hom c * z) ht
  exact hs.trans (congrArg (fun z => eb.inv z) hmul)

private lemma restrictionFrame_conjugate
    {A B C A' B' : AddCommGrpCat}
    (ra : A' ≅ A) (rb : B' ≅ B) (ea : A' ≅ C) (eb : B' ≅ C)
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : f' = ra.hom ≫ f ≫ rb.inv) :
    ea.inv ≫ f' ≫ eb.hom =
      (ra.symm ≪≫ ea).inv ≫ f ≫ (rb.symm ≪≫ eb).hom := by
  rw [h]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc]

private lemma actualPositiveRestrictedConjugate_top
    (j : Fin 4) {d : ℕ} (p : PolyA) (hp : p.IsHomogeneous d)
    (a b : ℕ) (h : a + d = b) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (q : Γ((U : Scheme), ⊤)) :
    ((p3PositiveTwistOpenIsoUnit K U j hU a).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (actualPositiveWeightedMultiplication p hp a b h) ≫
      (p3PositiveTwistOpenIsoUnit K U j hU b).hom).val.app (op ⊤) q =
      U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p) * q := by
  let H := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    (evaluation ((U : Scheme).Opens)ᵒᵖ AddCommGrpCat).obj (op ⊤)
  let ea := p3PositiveTwistOpenIsoUnit K U j hU a
  let eb := p3PositiveTwistOpenIsoUnit K U j hU b
  let f := actualPositiveWeightedMultiplication p hp a b h
  let R := Scheme.Modules.restrictFunctor U.ι
  let fa := ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U)
  let rA := moduleRestrictTopIso (positiveSheafOfModules PS a) U
  let rB := moduleRestrictTopIso (positiveSheafOfModules PS b) U
  let eA := H.mapIso ea
  let eB := H.mapIso eb
  have hlocal : H.map (R.map f) = rA.hom ≫ fa ≫ rB.inv :=
    moduleRestrictTopIso_local_map K f U
  have hconj := restrictionFrame_conjugate rA rB eA eB fa (H.map (R.map f)) hlocal
  have hmap : H.map (ea.inv ≫ R.map f ≫ eb.hom) =
      eA.inv ≫ H.map (R.map f) ≫ eB.hom := by
    rfl
  have hv := congrArg (fun k : H.obj (SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶
      H.obj (SheafOfModules.unit (U : Scheme).ringCatSheaf) => k q) (hmap.trans hconj)
  have hm := actualPositiveWeightedMultiplication_unitSectionsFrame j p hp a b h U hU q
  have he : (p3PositiveTwistSectionsIsoUnit K U j hU b).hom
      ((p3PositiveTwistSectionsIsoUnit K U j hU b).inv
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p) * q)) =
      U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p) * q :=
    ConcreteCategory.congr_hom (p3PositiveTwistSectionsIsoUnit K U j hU b).inv_hom_id _
  exact hv.trans ((congrArg (fun z =>
    (p3PositiveTwistSectionsIsoUnit K U j hU b).hom z) hm).trans he)

/-- ACTUAL restricted positive multiplication in the ACTUAL coordinate
unit frames equals the endomorphism of the literal normalized coefficient.
The equality follows from actual unit-Hom top1, not an assumed comparison. -/
theorem actualPositiveWeightedMultiplication_restrictedUnitCoefficient
    (j : Fin 4) {d : ℕ} (p : PolyA) (hp : p.IsHomogeneous d)
    (a b : ℕ) (h : a + d = b) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) :
    (p3PositiveTwistOpenIsoUnit K U j hU a).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (actualPositiveWeightedMultiplication p hp a b h) ≫
      (p3PositiveTwistOpenIsoUnit K U j hU b).hom =
    unitEndomorphismOfRegularFunction
      (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p)) := by
  let f := (p3PositiveTwistOpenIsoUnit K U j hU a).inv ≫
    (Scheme.Modules.restrictFunctor U.ι).map
      (actualPositiveWeightedMultiplication p hp a b h) ≫
    (p3PositiveTwistOpenIsoUnit K U j hU b).hom
  have hv : unitEndomorphismValue (X := (U : Scheme)) f =
      U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p) := by
    let c : Γ((U : Scheme), ⊤) :=
      U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU p)
    have ht : f.val.app (op ⊤) (1 : Γ((U : Scheme), ⊤)) =
        c * (1 : Γ((U : Scheme), ⊤)) :=
      actualPositiveRestrictedConjugate_top j p hp a b h U hU
        (1 : Γ((U : Scheme), ⊤))
    have hone : c * (1 : Γ((U : Scheme), ⊤)) = c := mul_one c
    change f.val.app (op ⊤) (1 : Γ((U : Scheme), ⊤)) = c
    exact ht.trans hone
  exact (unitEndomorphismOfRegularFunction_value f).symm.trans
    (congrArg (unitEndomorphismOfRegularFunction (X := (U : Scheme))) hv)

end PfaffianDescent.Coray
