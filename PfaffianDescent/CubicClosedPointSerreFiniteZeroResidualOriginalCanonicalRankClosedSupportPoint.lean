import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalRankClosedSupportPower
import AllCharacteristics.RelativeConfigurationPermutations
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_rankConfiguration_support_point_closed
    {K E : Type u} [Field K] [Field E] {X D B : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (d : D ⟶ Spec (.of K)) [IsFinite d]
    (i : D ⟶ X) (hi : i ≫ f = d)
    (a : B ⟶ (orderedFamilyConfigurationOver f 3).left) [IsOpenImmersion a]
    (c : Spec (.of E) ⟶ B) (r : Spec (.of E) ⟶ Spec (.of K))
    (δ : Fin 3 → (Spec (.of E) ⟶ D)) (hδd : ∀ n, δ n ≫ d = r)
    (hpoints : ∀ n, c ≫ a ≫ (orderedFamilyConfigurationι f 3).left ≫
      (orderedFamilyCoordinate f 3 n).left = δ n ≫ i) :
    IsClosed {c (IsLocalRing.closedPoint E)} := by
  let b := a ≫ (orderedFamilyConfigurationOver f 3).hom
  have hc : c ≫ b = r := by
    calc
      c ≫ b = (c ≫ a ≫ (orderedFamilyConfigurationι f 3).left ≫
          (orderedFamilyCoordinate f 3 0).left) ≫ f := by
        simp only [b, Category.assoc, orderedFamilyCoordinate_toBase]
        rfl
      _ = (δ 0 ≫ i) ≫ f := congrArg (fun q => q ≫ f) (hpoints 0)
      _ = r := by rw [Category.assoc, hi, hδd]
  let T := Over.mk r
  let h : Over.mk d ⟶ Over.mk f := Over.homMk i hi
  let v : T ⟶ orderedFamilyPowerOver d 3 :=
    orderedFamilyTuple d T 3 (fun n => Over.homMk (δ n) (hδd n))
  let q : T ⟶ orderedFamilyConfigurationOver f 3 :=
    Over.homMk (c ≫ a) (by
      change (c ≫ a) ≫ (orderedFamilyConfigurationOver f 3).hom = r
      simpa only [b, Category.assoc] using hc)
  have heq : v ≫ orderedFamilyMap d f h 3 = q ≫ orderedFamilyConfigurationι f 3 := by
    apply orderedFamilyPower_coordinate_ext f T 3
    intro n
    rw [Category.assoc, orderedFamilyMap_coordinate, ← Category.assoc,
      orderedFamilyTuple_coordinate]
    apply Over.OverMorphism.ext
    exact (hpoints n).symm
  let m := (orderedFamilyMap d f h 3).left
  letI : IsFinite (orderedFamilyPowerOver d 3).hom :=
    cubicClosedPointSerreFiniteZeroResidual_finite_orderedSupportPower d 3
  letI : IsFinite (m ≫ (orderedFamilyPowerOver f 3).hom) := by
    rw [show m ≫ (orderedFamilyPowerOver f 3).hom =
      (orderedFamilyPowerOver d 3).hom from (orderedFamilyMap d f h 3).w]
    infer_instance
  letI : IsFinite m := IsFinite.of_comp m (orderedFamilyPowerOver f 3).hom
  let y := v.left (IsLocalRing.closedPoint E)
  have hy : IsClosed {y} :=
    cubicClosedPointSerreFiniteZeroResidual_finiteOverField_point_closed
      (orderedFamilyPowerOver d 3).hom y
  have hm : IsClosed {m y} := by simpa only [Set.image_singleton] using m.isClosedMap _ hy
  letI : IsOpenImmersion (orderedFamilyConfigurationι f 3).left := by
    change IsOpenImmersion (orderedFamilyConfigurationOpen f 3).ι
    infer_instance
  let j := a ≫ (orderedFamilyConfigurationι f 3).left
  letI : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hmy : m y = j (c (IsLocalRing.closedPoint E)) := by
    have hh := congrArg (fun k => k.left (IsLocalRing.closedPoint E)) heq
    exact hh
  rw [hmy] at hm
  have hp := hm.preimage j.continuous
  convert hp using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact j.isOpenEmbedding.injective.eq_iff.symm
end PfaffianDescent
