import PfaffianDescent.MonomialCoefficientChartFaithfulness306
import PfaffianDescent.NativeCommonAffineChartCover306
import PfaffianDescent.NativeFixedBaseUniversalFamilyPullback305

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Transfer the fixed-base law to a chart factor before inserting the actual
coefficient quotient rings. -/
private lemma nativeChartFactorOverBase306
    {X U H S : Scheme.{u}} (v : X ⟶ S) (g : X ⟶ H)
    (a : X ⟶ U) (i : U ⟶ H) (b : H ⟶ S) (c : U ⟶ S)
    (hg : g ≫ b = v) (hi : i ≫ b = c) (ha : g = a ≫ i) : a ≫ c = v := by
  calc
    a ≫ c = a ≫ (i ≫ b) := congrArg (fun z => a ≫ z) hi.symm
    _ = (a ≫ i) ≫ b := (Category.assoc a i b).symm
    _ = g ≫ b := congrArg (fun z => z ≫ b) ha.symm
    _ = v := hg

set_option backward.isDefEq.respectTransparency.types false in
/-- Native uniqueness on the actual glued coefficient scheme. The common affine
chart refinement and both coefficient points are constructed internally.
The sole comparison input is equality of the entire pulled universal ideals. -/
theorem monomialGlobalClassifyingMap_unique306
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)
    (g h : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n)
    (hg : g ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hh : h ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hideal : (fixedBaseUniversalFamilyPullback305 R m n g hg).val =
      (fixedBaseUniversalFamilyPullback305 R m n h hh).val) : g = h := by
  obtain ⟨V, hV⟩ := nativeCommonAffineChartCover_exists306
    (monomialCoefficientGluedOpenCover300 R m n) g h
  apply V.openCover.hom_ext g h
  intro z
  obtain ⟨i, j, a, b, ha, hb⟩ := hV z
  obtain ⟨f, hf⟩ := Spec.map_surjective (V.f z)
  let T : Type u := V.X z
  letI : Algebra R T := (f.hom.comp (algebraMap R A)).toAlgebra
  let fa : A →ₐ[R] T := { f.hom with commutes' := fun _ => rfl }
  have hf' : Spec.map (CommRingCat.ofHom fa.toRingHom) = V.f z := hf
  have hs : (V.f z) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← hf, ← Spec.map_comp]
    rfl
  have hg' : (V.f z ≫ g) ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [Category.assoc, hg]
    exact hs
  have hh' : (V.f z ≫ h) ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [Category.assoc, hh]
    exact hs
  have haBase : a ≫ monomialCoefficientChartToBase300 R m n i.down.monomials i.down.zeroIndex =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
    nativeChartFactorOverBase306 _ (V.f z ≫ g) a
      (monomialCoefficientGluedChartMap300 R m n i.down)
      (monomialCoefficientGluedToBase300 R m n) _ hg'
      (monomialCoefficientGluedChartMap_toBase300 R m n i.down) ha
  have hbBase : b ≫ monomialCoefficientChartToBase300 R m n j.down.monomials j.down.zeroIndex =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
    nativeChartFactorOverBase306 _ (V.f z ≫ h) b
      (monomialCoefficientGluedChartMap300 R m n j.down)
      (monomialCoefficientGluedToBase300 R m n) _ hh'
      (monomialCoefficientGluedChartMap_toBase300 R m n j.down) hb
  obtain ⟨p, hp⟩ := nativeAffineMapOverBase_algHom_exists306 R
    (C := UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex)
    (T := T) a haBase
  obtain ⟨q, hq⟩ := nativeAffineMapOverBase_algHom_exists306 R
    (C := UniversalCyclicCoefficientAlgebra282 R m n j.down.monomials j.down.zeroIndex)
    (T := T) b hbBase
  have hpg : Spec.map (CommRingCat.ofHom fa.toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n i.down := by
    rw [hf', hp]
    exact ha
  have hqh : Spec.map (CommRingCat.ofHom fa.toRingHom) ≫ h =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n j.down := by
    rw [hf', hq]
    exact hb
  have hlocal := congrArg
    (fun J : (Spec (.of (MvPolynomial (Fin m) A))).IdealSheafData =>
      J.comap (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) fa.toRingHom)))) hideal
  have hpIdeal := fixedBaseUniversalFamilyPullback_chartIdeal305 R m n g hg i.down fa p hpg
  have hqIdeal := fixedBaseUniversalFamilyPullback_chartIdeal305 R m n h hh j.down fa q hqh
  have he := monomialCoefficientChartMaps_eq_of_wholeFamily306 R i.down j.down p q
    (hpIdeal.symm.trans (hlocal.trans hqIdeal))
  exact ha.trans ((congrArg
    (fun k => k ≫ monomialCoefficientGluedChartMap300 R m n i.down) hp).symm.trans
      (he.trans ((congrArg
        (fun k => k ≫ monomialCoefficientGluedChartMap300 R m n j.down) hq).trans hb.symm)))

/-- Literal global whole-ideal formulation of native uniqueness on the actual
H-scheme. The ambient maps are the canonical fixed-base Cartesian maps305. -/
theorem monomialGlobalClassifyingMap_unique_of_globalWholeIdeal306
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)
    (g h : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n)
    (hg : g ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hh : h ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hideal : (monomialCoefficientUniversalWholeIdeal300 R m n).comap
        (fixedBaseTestAmbientMap305 R m n g hg) =
      (monomialCoefficientUniversalWholeIdeal300 R m n).comap
        (fixedBaseTestAmbientMap305 R m n h hh)) : g = h :=
  monomialGlobalClassifyingMap_unique306 R m n g h hg hh hideal

end PfaffianDescent
end
