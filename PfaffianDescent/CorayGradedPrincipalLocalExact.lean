import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.GradedSurjection

/-! The homogeneous denominator-clearing calculation needed for q on the
actual cubic quotient. The target ring need not be a domain. The generic
kernel hypothesis is discharged from the literal (p,q) quotient by the
geometric caller; it is not a certificate in that caller.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open scoped DirectSum Pointwise
open AlgebraicGeometry CategoryTheory DirectSum SetLike Localization
open ProjectiveNegativeTwist
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The complementary-degree factor calculation works in the actual graded
quotient ring, not only in a polynomial ring. -/
theorem gradedPrincipal_homogeneous_factor
    {i d : ℕ} (s : 𝒜 d) (a : 𝒜 i)
    (ha : (a : A) ∈ Ideal.span ({(s : A)} : Set A)) :
    (d ≤ i → ∃ c : 𝒜 (i - d), (s : A) * c = a) ∧
      (¬ d ≤ i → (a : A) = 0) := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  constructor
  · intro hdi
    refine ⟨DirectSum.decompose 𝒜 r (i - d), ?_⟩
    rw [← DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 s.2 hdi,
      ← hr]
    exact DirectSum.decompose_of_mem_same 𝒜 a.2
  · intro hdi
    rw [← DirectSum.decompose_of_mem_same 𝒜 a.2, hr]
    exact DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 s.2 hdi

/-- A zero image of a homogeneous local fraction admits a HOMOGENEOUS
annihilating multiplier outside the source prime. This removes the old
domain-target assumption and covers literal nonreduced intersections. -/
theorem gradedPrincipal_homogeneous_annihilator
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : HomogeneousIdeal ℬ) [Q.toIdeal.IsPrime]
    (hPQ : P = Ideal.comap f.toRingHom Q.toIdeal)
    (c : HomogeneousLocalization.NumDenSameDeg 𝒜 P.primeCompl)
    (hzero : HomogeneousLocalization.localRingHom f P Q.toIdeal hPQ
      (HomogeneousLocalization.mk c) = 0) :
    ∃ (j : ℕ) (t : 𝒜 j), (t : A) ∈ P.primeCompl ∧ f ((t : A) * c.num) = 0 := by
  classical
  have hval := congrArg HomogeneousLocalization.val hzero
  rw [HomogeneousLocalization.val_localRingHom,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Localization.localRingHom_mk, Localization.mk_eq_mk'] at hval
  obtain ⟨b, hb⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  change (b : B) * f c.num = 0 at hb
  have hex : ∃ j, (DirectSum.decompose ℬ (b : B) j : B) ∉ Q.toIdeal := by
    by_contra hn
    apply b.2
    apply Q.isHomogeneous.mem_iff.mpr
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  obtain ⟨a, ha, hfa⟩ := gradedSurjective_homogeneous_lift f hf j
    (DirectSum.decompose ℬ (b : B) j) (DirectSum.decompose ℬ (b : B) j).2
  let t : 𝒜 j := ⟨a, ha⟩
  have ht : (t : A) ∈ P.primeCompl := by
    intro htP
    apply hj
    rw [hPQ] at htP
    change f a ∈ Q.toIdeal at htP
    rwa [hfa] at htP
  have hmul : (DirectSum.decompose ℬ (b : B) j : B) * f c.num = 0 := by
    calc
      _ = (DirectSum.decompose ℬ ((b : B) * f c.num) (j + c.deg) : B) :=
        (DirectSum.coe_decompose_mul_add_of_right_mem ℬ (f.map_mem c.num.2)).symm
      _ = 0 := by rw [hb]; simp
  refine ⟨j, t, ht, ?_⟩
  rw [map_mul]
  change f a * f c.num = 0
  rw [hfa]
  exact hmul

/-- Exactness of multiplication and the actual homogeneous local-ring map
for a surjective graded map with principal homogeneous kernel. No domain,
reducedness, flatness or assumed local exactness is required. -/
theorem gradedPrincipal_localRing_exact
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {d : ℕ} (s : 𝒜 d)
    (hker : RingHom.ker f.toRingHom = Ideal.span ({(s : A)} : Set A))
    (y : ProjectiveSpectrum ℬ) :
    let h := gradedSurjective_irrelevant_le f hf
    let x := ProjectiveSpectrum.comap f h y
    Function.Exact
      (fun z : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal (0 + d) =>
        (atPrimeLinearEquivZeroTwistStalk 𝒜 x.asHomogeneousIdeal.toIdeal).symm
          (mulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal s 0 z))
      (HomogeneousLocalization.localRingHom f
        x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal rfl) := by
  dsimp only
  let h := gradedSurjective_irrelevant_le f hf
  let x := ProjectiveSpectrum.comap f h y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let P := x.asHomogeneousIdeal.toIdeal
  let Q := y.asHomogeneousIdeal.toIdeal
  have hPQ : P = Ideal.comap f.toRingHom Q := rfl
  let e := atPrimeLinearEquivZeroTwistStalk 𝒜 P
  let F := fun z : stalkSubmodule 𝒜 P (0 + d) =>
    e.symm (mulHomogeneousStalk 𝒜 P s 0 z)
  let G := HomogeneousLocalization.localRingHom f P Q hPQ
  change Function.Exact F G
  intro z
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := HomogeneousLocalization.mk_surjective z
    have hzc : G (HomogeneousLocalization.mk c) = 0 := by rw [hc]; exact hz
    obtain ⟨j, t, ht, htc⟩ := gradedPrincipal_homogeneous_annihilator 𝒜 ℬ
      f hf P y.asHomogeneousIdeal hPQ c hzc
    let a : 𝒜 (j + c.deg) :=
      ⟨(t : A) * c.num, SetLike.mul_mem_graded t.2 c.num.2⟩
    have ha : (a : A) ∈ Ideal.span ({(s : A)} : Set A) := by
      rw [← hker]
      exact htc
    have hfactor := gradedPrincipal_homogeneous_factor 𝒜 s a ha
    let b : 𝒜 (j + c.deg) :=
      ⟨(t : A) * c.den, SetLike.mul_mem_graded t.2 c.den.2⟩
    have hb : (b : A) ∈ P.primeCompl := P.primeCompl.mul_mem ht c.den_mem
    have hclear : Localization.mk (a : A) ⟨(b : A), hb⟩ =
        (HomogeneousLocalization.mk c).val := by
      rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
        IsLocalization.mk'_eq_iff_eq]
      congr 1
      dsimp only [a, b]
      ring
    by_cases hdi : d ≤ j + c.deg
    · obtain ⟨v, hv⟩ := hfactor.1 hdi
      let den : 𝒜 (((j + c.deg) - d) + (0 + d)) :=
        ⟨b, by simpa only [Nat.zero_add, Nat.sub_add_cancel hdi] using b.2⟩
      let w : stalkSubmodule 𝒜 P (0 + d) :=
        ⟨Localization.mk (v : A) ⟨(b : A), hb⟩,
          Or.inr ⟨(j + c.deg) - d, v, den, hb, rfl⟩⟩
      refine ⟨w, ?_⟩
      rw [← hc]
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      change algebraMap A (Localization P.primeCompl) (s : A) *
        Localization.mk (v : A) ⟨(b : A), hb⟩ = _
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, hv]
      change Localization.mk (a : A) (1 * ⟨(b : A), hb⟩) =
        (HomogeneousLocalization.mk c).val
      simpa only [one_mul] using hclear
    · have ha0 : (a : A) = 0 := hfactor.2 hdi
      refine ⟨0, ?_⟩
      rw [← hc]
      apply e.injective
      dsimp only [F]
      rw [e.apply_symm_apply, map_zero]
      apply Subtype.ext
      change (0 : Localization P.primeCompl) = (HomogeneousLocalization.mk c).val
      rw [← hclear, ha0, Localization.mk_zero]
  · rintro ⟨w, hw⟩
    have hs0 : f s = 0 := by
      change (s : A) ∈ RingHom.ker f.toRingHom
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hval : (F w).val = algebraMap A (Localization P.primeCompl) (s : A) * w.1 :=
      congrArg Subtype.val (e.apply_symm_apply (mulHomogeneousStalk 𝒜 P s 0 w))
    have hG : G (F w) = 0 := by
      apply HomogeneousLocalization.val_injective Q.primeCompl
      let g : Localization P.primeCompl →+* Localization Q.primeCompl :=
        Localization.localRingHom P Q f.toRingHom hPQ
      have hsmap : g (algebraMap A (Localization P.primeCompl) (s : A)) = 0 := by
        change Localization.localRingHom P Q f.toRingHom hPQ
          (algebraMap A (Localization P.primeCompl) (s : A)) = 0
        rw [← Localization.mk_one_eq_algebraMap]
        simp only [Localization.localRingHom_mk,
          GradedRingHom.toRingHom_eq_toRingHom, GradedRingHom.coe_toRingHom,
          hs0, Localization.mk_zero]
      calc
        (G (F w)).val = g (F w).val :=
          HomogeneousLocalization.val_localRingHom (F w)
        _ = g (algebraMap A (Localization P.primeCompl) (s : A) * w.1) :=
          congrArg g hval
        _ = g (algebraMap A (Localization P.primeCompl) (s : A)) * g w.1 :=
          map_mul g _ _
        _ = 0 * g w.1 :=
          congrArg (fun v : Localization Q.primeCompl => v * g w.1) hsmap
        _ = 0 := zero_mul _
        _ = (0 : HomogeneousLocalization.AtPrime ℬ Q).val :=
          HomogeneousLocalization.val_zero.symm
    exact (congrArg G hw).symm.trans hG

/-- Actual categorical stalk compatibility for multiplication into the unit
on an arbitrary graded ring. The polynomial-specialized producer's proof
uses only these generic constructions, so it applies to the cubic quotient. -/
theorem gradedPrincipal_mulToUnit_stalkMap_compat
    {d : ℕ} (s : 𝒜 d) (x : Proj 𝒜)
    (z : (sheafOfModules 𝒜 (0 + d)).presheaf.stalk x) :
    Proj.stalkIso' 𝒜 x
      ((presheafOfModules_unitStalkLinearEquiv
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x).symm
        ((schemeModuleStalkFunctor (Proj 𝒜) x).map (mulHomogeneousToUnit 𝒜 s) z)) =
    (atPrimeLinearEquivZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)).symm
      (mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s 0
        (stalkToFractionModule 𝒜 (0 + d) x z)) := by
  let u := presheafOfModules_unitStalkLinearEquiv
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x
  let p := Proj.stalkIso' 𝒜 x
  let e := atPrimeLinearEquivZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
  let t := stalkToFractionModule 𝒜 0 x
  let g := (schemeModuleStalkFunctor (Proj 𝒜) x).map (mulHomogeneousToUnit 𝒜 s)
  let h := (schemeModuleStalkFunctor (Proj 𝒜) x).map (unitToZeroTwist 𝒜)
  let m := (schemeModuleStalkFunctor (Proj 𝒜) x).map (mulHomogeneous 𝒜 s 0)
  have hcomp : mulHomogeneousToUnit 𝒜 s ≫ unitToZeroTwist 𝒜 =
      mulHomogeneous 𝒜 s 0 := by
    let e0 := unitIsoZeroTwist 𝒜
    change (mulHomogeneous 𝒜 s 0 ≫ e0.inv) ≫ e0.hom = _
    rw [Category.assoc, e0.inv_hom_id, Category.comp_id]
  have hmaps := congrArg (fun q => (schemeModuleStalkFunctor (Proj 𝒜) x).map q) hcomp
  rw [Functor.map_comp] at hmaps
  have hpoint : h (g z) = m z :=
    DFunLike.congr_fun (congrArg ConcreteCategory.hom hmaps) z
  have hu := unitToZeroTwist_stalkMap_compat 𝒜 x (u.symm (g z))
  change t (h (u (u.symm (g z)))) = e (p (u.symm (g z))) at hu
  rw [u.apply_symm_apply] at hu
  apply e.injective
  rw [e.apply_symm_apply]
  calc
    e (p (u.symm (g z))) = t (h (g z)) := hu.symm
    _ = t (m z) := congrArg t hpoint
    _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s 0
        (stalkToFractionModule 𝒜 (0 + d) x z) :=
      stalkToFractionModule_stalkMap 𝒜 s 0 x z

end PfaffianDescent.Coray
