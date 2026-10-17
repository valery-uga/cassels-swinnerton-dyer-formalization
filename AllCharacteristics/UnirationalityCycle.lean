import AllCharacteristics.ProperCyclePushforward
import AllCharacteristics.EffectiveCycleToZeroCycle
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Zero-cycles from domains of rational maps

This is the cycle-theoretic bridge used in the unirationality corollary:
a finite algebra point at which a rational map is defined yields an effective
cycle of the same degree on its target.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
namespace HomogeneousProjective

universe u v

/-- A finite algebra point lying in the domain of a partial rational map
pushes forward to an effective cycle of the same degree on the target. -/
theorem effectiveZeroCycle_of_partialMap_finiteAlgebraPoint
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {X Y : Scheme.{u}}
    (xBase : X ⟶ Spec (.of k)) (yBase : Y ⟶ Spec (.of k)) [IsSeparated yBase]
    (f : X.PartialMap Y)
    (hbase : f.hom ≫ yBase = f.domain.ι ≫ xBase)
    (q : Spec (.of A) ⟶ f.domain)
    (hq : q ≫ f.domain.ι ≫ xBase =
      Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ z : EffectiveZeroCycle Y,
      EffectiveZeroCycle.degree yBase z = Module.finrank k A := by
  apply exists_effectiveZeroCycle_of_finite_algebra_point yBase (q ≫ f.hom)
  rw [Category.assoc, hbase]
  simpa only [Category.assoc] using hq

/-- A ground-field point in the domain of a partial rational map gives an
actual degree-one zero-cycle on its separated target. -/
theorem zeroCycle_degree_one_of_partialMap_domain_section
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (xBase : X ⟶ Spec (.of k)) (yBase : Y ⟶ Spec (.of k)) [IsSeparated yBase]
    (f : X.PartialMap Y)
    (hbase : f.hom ≫ yBase = f.domain.ι ≫ xBase)
    (q : Spec (.of k) ⟶ f.domain)
    (hq : q ≫ f.domain.ι ≫ xBase = 𝟙 _) :
    ∃ z : ZeroCycle Y, ZeroCycle.degree yBase z = 1 := by
  obtain ⟨z, hz⟩ := effectiveZeroCycle_of_partialMap_finiteAlgebraPoint
    xBase yBase f hbase q (by simpa using hq)
  refine ⟨z.toZeroCycle, ?_⟩
  rw [EffectiveZeroCycle.degree_toZeroCycle, hz]
  simp


/-- A nonzero multivariable polynomial over an infinite field is nonzero at
some rational point. -/
theorem exists_mvPolynomial_eval_ne_zero_of_infinite
    {K : Type u} {σ : Type v} [Field K] [Infinite K] [Finite σ]
    (p : MvPolynomial σ K) (hp : p ≠ 0) :
    ∃ a : σ → K, MvPolynomial.eval a p ≠ 0 := by
  classical
  choose S hS using fun i => Infinite.exists_subset_card_eq K (p.degreeOf i + 1)
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p S
  · intro i
    rw [hS i]
    omega
  · intro a ha
    exact h a

/-- A nonvanishing evaluation of a function produces a point of every open
set containing its basic open. -/
theorem exists_rational_point_of_spec_basicOpen_le
    {K R : Type u} [Field K] [CommRing R]
    (U : Scheme.Opens (Spec (.of R))) (g : R)
    (hUg : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g) ≤ U)
    (φ : R →+* K) (hφ : φ g ≠ 0) :
    ∃ q : Spec (.of K) ⟶ U,
      q ≫ U.ι = Spec.map (CommRingCat.ofHom φ) := by
  let qBasic : Spec (.of K) ⟶ _ :=
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift g hφ.isUnit)) ≫
      (basicOpenIsoSpecAway (R := CommRingCat.of R) g).inv
  have e : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g) =
      PrimeSpectrum.basicOpen g :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) g
  refine ⟨qBasic ≫ Scheme.homOfLE (Spec (.of R)) e.symm.le ≫
    Scheme.homOfLE (Spec (.of R)) hUg, ?_⟩
  rw [← Category.assoc, Category.assoc, Scheme.homOfLE_ι, Category.assoc]
  have hfac := Scheme.homOfLE_ι (Spec (.of R)) e.symm.le
  rw [hfac]
  have hIso := basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) g
  rw [← hIso]
  dsimp [qBasic]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact congrArg CommRingCat.ofHom
    (IsLocalization.Away.lift_comp (S := Localization.Away g) g hφ.isUnit)

/-- A dense open subscheme of affine space over an infinite field has a
rational section over the ground field. -/
theorem dense_open_affineSpace_has_rational_section
    {K σ : Type u} [Field K] [Infinite K] [Finite σ]
    (D : Scheme.Opens (AffineSpace σ (Spec (.of K))))
    (hD : Dense (D : Set (AffineSpace σ (Spec (.of K))))) :
    ∃ q : Spec (.of K) ⟶ D,
      q ≫ D.ι ≫ (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K)) = 𝟙 _ := by
  let e : AffineSpace σ (Spec (.of K)) ≅ Spec (.of (MvPolynomial σ K)) :=
    AffineSpace.SpecIso σ (.of K)
  let Dspec : Scheme.Opens (Spec (.of (MvPolynomial σ K))) := e.inv ⁻¹ᵁ D
  have hDspec : Dense (Dspec : Set (Spec (.of (MvPolynomial σ K)))) := by
    change Dense ((e.inv : Spec (.of (MvPolynomial σ K)) ⟶
      AffineSpace σ (Spec (.of K))) ⁻¹' (D : Set _))
    exact hD.preimage e.inv.homeomorph.isOpenMap
  obtain ⟨x, hx⟩ := hDspec.nonempty
  obtain ⟨f, hfD, hxf⟩ :=
    (isAffineOpen_top (Spec (.of (MvPolynomial σ K)))).exists_basicOpen_le
      (V := Dspec) ⟨x, hx⟩ trivial
  let g : MvPolynomial σ K := (Scheme.ΓSpecIso (.of (MvPolynomial σ K))).hom f
  have hg : g ≠ 0 := by
    intro hg
    have hfg : f = 0 := by
      have h' := congrArg (fun z => (Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv z) hg
      simpa [g] using h'
    subst hfg
    simp at hxf
  obtain ⟨a, ha⟩ := exists_mvPolynomial_eval_ne_zero_of_infinite g hg
  have hgD : (Spec (.of (MvPolynomial σ K))).basicOpen
      ((Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv g) ≤ Dspec := by
    simpa [g] using hfD
  obtain ⟨q, hq⟩ := exists_rational_point_of_spec_basicOpen_le
    Dspec g hgD (MvPolynomial.aeval (R := K) a).toRingHom ha
  have hqbase : q ≫ Dspec.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K))) = 𝟙 _ := by
    rw [← Category.assoc, hq]
    have hbase :
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact (MvPolynomial.aeval (R := K) a).comp_algebraMap
    rw [hbase]
    simp
  let i : Dspec.toScheme ≅ D := e.inv.preimageIso D
  refine ⟨q ≫ i.hom, ?_⟩
  have hi : i.hom ≫ D.ι = Dspec.ι ≫ e.inv := by
    dsimp [i, Dspec]
    exact Scheme.Hom.preimageIso_hom_ι e.inv D
  calc
    (q ≫ i.hom) ≫ D.ι ≫ (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K)) =
        q ≫ (i.hom ≫ D.ι) ≫ (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K)) := by
          simp only [Category.assoc]
    _ = q ≫ (Dspec.ι ≫ e.inv) ≫
        (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K)) := by rw [hi]
    _ = q ≫ Dspec.ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial σ K))) := by
          simp only [Category.assoc, e, AffineSpace.SpecIso_inv_over]
          have hC : (MvPolynomial.C : K →+* MvPolynomial σ K) =
              algebraMap K (MvPolynomial σ K) := rfl
          rw [hC]
    _ = 𝟙 _ := hqbase

/-- A partial rational map from affine space over an infinite field yields a
zero-cycle of degree one on a separated target. -/
theorem zeroCycle_degree_one_of_affine_partialMap_infinite
    {K σ : Type u} [Field K] [Infinite K] [Finite σ]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsSeparated y]
    (f : (AffineSpace σ (Spec (.of K))).PartialMap Y)
    (hbase : f.hom ≫ y = f.domain.ι ≫
      (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K))) :
    ∃ z : ZeroCycle Y, ZeroCycle.degree y z = 1 := by
  obtain ⟨q, hq⟩ := dense_open_affineSpace_has_rational_section
    f.domain f.dense_domain
  exact zeroCycle_degree_one_of_partialMap_domain_section _ y f hbase q hq

end HomogeneousProjective
end AllCharacteristics
