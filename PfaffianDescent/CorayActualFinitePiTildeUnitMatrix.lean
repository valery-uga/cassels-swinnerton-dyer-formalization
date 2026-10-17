import PfaffianDescent.CorayActualPositiveBasicOpenSpecCoefficient
import PfaffianDescent.AffineQuotientPushforwardTilde
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Pi

/-! Literal finite Pi-module coproducts under the actual tilde functor.
The inclusions and scalar maps are computed in the original ring/module
structures. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open BundleSectionZeroLocus
open scoped BigOperators
universe u

/-- The actual single-coordinate map into the finite Pi module. -/
def actualFinitePiInjection (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] (i : ι) :
    ModuleCat.of B B ⟶ ModuleCat.of B (ι → B) := by
  classical
  exact ModuleCat.ofHom (LinearMap.single B (fun _ : ι => B) i)

private def actualFinitePiCofan (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] : Cofan (fun _ : ι => ModuleCat.of B B) :=
  Cofan.mk (ModuleCat.of B (ι → B)) (actualFinitePiInjection B ι)

private def actualFinitePiCofan_isColimit (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] : IsColimit (actualFinitePiCofan B ι) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun s => ModuleCat.ofHom (∑ i, (s.inj i).hom.comp (LinearMap.proj i))) ?_ ?_
  · intro s i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (∑ j, (s.inj j).hom.comp (LinearMap.proj j))
      (Pi.single i (show B from x) : ι → B) = (s.inj i).hom x
    have heval : (∑ j, (s.inj j).hom.comp (LinearMap.proj j))
        (Pi.single i (show B from x) : ι → B) =
        ∑ j, (s.inj j).hom ((Pi.single i (show B from x) : ι → B) j) :=
      LinearMap.sum_apply Finset.univ
        (fun j => (s.inj j).hom.comp (LinearMap.proj j))
        (Pi.single i (show B from x) : ι → B)
    have hsum : (∑ j, (s.inj j).hom
        ((Pi.single i (show B from x) : ι → B) j)) =
        (s.inj i).hom ((Pi.single i (show B from x) : ι → B) i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hz : (Pi.single i (show B from x) : ι → B) j = 0 := by
          simp only [Pi.single_apply, if_neg hji]
        exact (congrArg (s.inj j).hom hz).trans (s.inj j).hom.map_zero
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hsingle : (Pi.single i (show B from x) : ι → B) i = x := by
      simp only [Pi.single_apply, if_true]
    exact heval.trans (hsum.trans (congrArg (s.inj i).hom hsingle))
  · intro s m h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change m.hom x = (∑ i, (s.inj i).hom.comp (LinearMap.proj i)) x
    have heval : (∑ i, (s.inj i).hom.comp (LinearMap.proj i)) x =
        ∑ i, (s.inj i).hom (x i) :=
      LinearMap.sum_apply Finset.univ
        (fun i => (s.inj i).hom.comp (LinearMap.proj i)) (show ι → B from x)
    have hx : (∑ i, (Pi.single i (x i) : ι → B)) = x :=
      LinearMap.sum_single_apply (fun _ : ι => B) (show ι → B from x)
    have hsum : (∑ i, m.hom (Pi.single i (x i) : ι → B)) =
        ∑ i, (s.inj i).hom (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun f : ModuleCat.of B B ⟶ s.pt => f.hom (x i)) (h i)
    exact (congrArg m.hom hx.symm).trans ((map_sum m.hom _ _).trans
      (hsum.trans heval.symm))

private def actualFinitePiTildeCofan (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] :
    Cofan (fun _ : ι => SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :=
  Cofan.mk ((tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (ι → B)))
    (fun i => (tildeSelf (R := CommRingCat.of B)).inv ≫
      (tilde.functor (CommRingCat.of B)).map (actualFinitePiInjection B ι i))

private def actualFinitePiTildeCofan_isColimit (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] : IsColimit (actualFinitePiTildeCofan B ι) := by
  let F := tilde.functor (CommRingCat.of B)
  letI : F.IsLeftAdjoint := (tilde.adjunction (R := CommRingCat.of B)).isLeftAdjoint
  let H := isColimitOfPreserves F (actualFinitePiCofan_isColimit B ι)
  let e : (Discrete.functor (fun _ : ι => ModuleCat.of B B)) ⋙ F ≅
      Discrete.functor (fun _ : ι => SheafOfModules.unit
        (Spec (CommRingCat.of B)).ringCatSheaf) :=
    Discrete.natIso (fun _ => tildeSelf)
  exact (IsColimit.precomposeHomEquiv e.symm _).symm H

/-- Actual tilde of the OWN finite Pi module is framed by the canonical
coproduct of units, with no free-module equivalence supplied as a premise. -/
def actualFinitePiTildeUnitIso (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] :
    (∐ fun _ : ι => SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) ≅
      (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (ι → B)) :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _)
    (actualFinitePiTildeCofan_isColimit B ι)

/-- Its component is tilde of the literal single-coordinate injection,
through Mathlib's original tilde-self/unit comparison. -/
@[reassoc]
theorem actualFinitePiTildeUnitIso_inclusion (B : Type u) [CommRing B]
    (ι : Type u) [Fintype ι] (i : ι) :
    Sigma.ι (fun _ : ι => SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) i ≫
      (actualFinitePiTildeUnitIso B ι).hom =
    (tildeSelf (R := CommRingCat.of B)).inv ≫
      (tilde.functor (CommRingCat.of B)).map (actualFinitePiInjection B ι i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (actualFinitePiTildeCofan_isColimit B ι) (Discrete.mk i)

/-- Multiplication by a native chart coefficient in its OWN ring module. -/
def actualRingMultiplicationMap (B : Type u) [CommRing B] (c : B) : B →ₗ[B] B where
  toFun x := c * x
  map_add' x y := mul_add c x y
  map_smul' a x := by
    change c * (a * x) = a * (c * x)
    exact mul_left_comm c a x

/-- Native tilde of multiplication, in the actual tilde-self frame, equals
multiplication by the canonical Gamma-Spec image of the SAME coefficient.
This follows from the tilde adjunction's actual unit naturality and top1. -/
theorem actualRingMultiplicationMap_tilde_unitCoefficient
    (B : Type u) [CommRing B] (c : B) :
    (tildeSelf (R := CommRingCat.of B)).inv ≫
      (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom (actualRingMultiplicationMap B c)) ≫
      (tildeSelf (R := CommRingCat.of B)).hom =
    unitEndomorphismOfRegularFunction ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom c) := by
  let R := CommRingCat.of B
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let O : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let e := PfaffianDescent.affineGlobalSectionsUnitLinearEquiv (A := B)
  let f : O ⟶ O := F.map (ModuleCat.ofHom (actualRingMultiplicationMap B c))
  let eta := tilde.toTildeΓNatIso (R := R)
  have heta : eta.hom.app (ModuleCat.of B B) = e.symm.toModuleIso.hom :=
    (PfaffianDescent.affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit
      (A := B)).symm
  have hn := eta.hom.naturality (ModuleCat.ofHom (actualRingMultiplicationMap B c))
  rw [heta] at hn
  have ht := congrArg (fun k : ModuleCat.of B B ⟶ G.obj O => k.hom (1 : B)) hn
  change e.symm (c * 1) = (G.map f).hom (e.symm 1) at ht
  have heone : e.symm (1 : B) = (show G.obj O from (1 : Γ(Spec R, ⊤))) := by
    change (Scheme.ΓSpecIso R).inv.hom (1 : B) = (1 : Γ(Spec R, ⊤))
    exact (Scheme.ΓSpecIso R).inv.hom.map_one
  have hec : e.symm c = (Scheme.ΓSpecIso R).inv.hom c := rfl
  have hv : unitEndomorphismValue (X := Spec R) f = (Scheme.ΓSpecIso R).inv.hom c := by
    change (G.map f).hom (show G.obj O from (1 : Γ(Spec R, ⊤))) = _
    have h₁ : (G.map f).hom (show G.obj O from (1 : Γ(Spec R, ⊤))) =
        (G.map f).hom (e.symm (1 : B)) :=
      congrArg (fun z : G.obj O => (G.map f).hom z) heone.symm
    have h₂ : (G.map f).hom (e.symm (1 : B)) = e.symm (c * 1) := ht.symm
    have h₃ : e.symm (c * 1) = e.symm c := congrArg e.symm (mul_one c)
    exact h₁.trans (h₂.trans (h₃.trans hec))
  change f = unitEndomorphismOfRegularFunction ((Scheme.ΓSpecIso R).inv.hom c)
  exact (unitEndomorphismOfRegularFunction_value (X := Spec R) f).symm.trans
    (congrArg (unitEndomorphismOfRegularFunction (X := Spec R)) hv)

end PfaffianDescent.Coray
