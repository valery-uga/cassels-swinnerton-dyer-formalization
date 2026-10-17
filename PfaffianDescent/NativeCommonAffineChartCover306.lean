import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Bound the three-leg factorization before inserting affine cover aliases. -/
private lemma nativeThreeLegChartFactor306
    {C : Type*} [Category C] {Z P Q U X Y : C}
    (e : Z ⟶ P) (t : P ⟶ Q) (s : Q ⟶ X) (a : Q ⟶ U)
    (i : U ⟶ Y) (g : X ⟶ Y) (f : Z ⟶ X) (w : P ⟶ X)
    (he : e ≫ w = f) (hw : w = t ≫ s) (hs : s ≫ g = a ≫ i) :
    f ≫ g = (e ≫ t ≫ a) ≫ i := by
  rw [← he, hw]
  simp only [Category.assoc]
  rw [hs]

/-- Bound the factorization for the second pulled cover before native substitution. -/
private lemma nativeCompositeChartFactor306
    {C : Type*} [Category C] {Z P Q U X Y : C}
    (e : Z ⟶ P) (t : P ⟶ Q) (s : Q ⟶ X) (b : P ⟶ U)
    (i : U ⟶ Y) (g : X ⟶ Y) (f : Z ⟶ X) (w : P ⟶ X)
    (he : e ≫ w = f) (hw : w = t ≫ s) (ht : t ≫ (s ≫ g) = b ≫ i) :
    f ≫ g = (e ≫ b) ≫ i := by
  rw [← he, hw]
  simp only [Category.assoc]
  rw [ht]

/-- Any two maps to an actually covered scheme acquire simultaneous chart
factorizations on an internally constructed common affine open cover. -/
lemma nativeCommonAffineChartCover_exists306
    {X Y : Scheme.{u}} (U : Y.OpenCover.{u}) (g h : X ⟶ Y) :
    ∃ V : X.AffineOpenCover.{u}, ∀ z : V.I₀,
      ∃ i j : U.I₀,
      ∃ a : Spec (V.X z) ⟶ U.X i,
      ∃ b : Spec (V.X z) ⟶ U.X j,
        V.f z ≫ g = a ≫ U.f i ∧ V.f z ≫ h = b ≫ U.f j := by
  let G := U.pullback₁ g
  let H (i : G.I₀) := U.pullback₁ (G.f i ≫ h)
  let W : X.OpenCover.{u} := G.bind H
  let V := W.affineRefinement
  let r : V.openCover ⟶ W := W.fromAffineRefinement
  refine ⟨V, ?_⟩
  intro z
  let k := r.s₀ z
  refine ⟨k.1, k.2,
    r.h₀ z ≫ (H k.1).f k.2 ≫ U.pullbackHom g k.1,
    r.h₀ z ≫ U.pullbackHom (G.f k.1 ≫ h) k.2, ?_, ?_⟩
  · have hr : r.h₀ z ≫ W.f k = V.f z := by
      change r.h₀ z ≫ W.f k = V.openCover.f z
      exact r.w₀ z
    exact nativeThreeLegChartFactor306 (C := Scheme.{u})
      (r.h₀ z) ((H k.1).f k.2) (G.f k.1) (U.pullbackHom g k.1)
      (U.f k.1) g (V.f z) (W.f k) hr rfl (U.pullbackHom_map g k.1).symm
  · have hr : r.h₀ z ≫ W.f k = V.f z := by
      change r.h₀ z ≫ W.f k = V.openCover.f z
      exact r.w₀ z
    exact nativeCompositeChartFactor306 (C := Scheme.{u})
      (r.h₀ z) ((H k.1).f k.2) (G.f k.1) (U.pullbackHom (G.f k.1 ≫ h) k.2)
      (U.f k.2) h (V.f z) (W.f k) hr rfl
      (U.pullbackHom_map (G.f k.1 ≫ h) k.2).symm

/-- Every native map of affine spectra over the fixed base is the Spec map
of an actual algebra homomorphism, extracted by full faithfulness. -/
lemma nativeAffineMapOverBase_algHom_exists306
    (R : Type u) [CommRing R] {C T : Type u} [CommRing C] [CommRing T]
    [Algebra R C] [Algebra R T] (a : Spec (.of T) ⟶ Spec (.of C))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    ∃ p : C →ₐ[R] T, Spec.map (CommRingCat.ofHom p.toRingHom) = a := by
  obtain ⟨f, hf⟩ := Spec.map_surjective a
  have hs : CommRingCat.ofHom (algebraMap R C) ≫ f =
      CommRingCat.ofHom (algebraMap R T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf]
    exact ha
  let p : C →ₐ[R] T :=
    { f.hom with
      commutes' := fun r => congrArg (fun z : CommRingCat.of R ⟶ CommRingCat.of T => z r) hs }
  exact ⟨p, hf⟩

end PfaffianDescent
end
