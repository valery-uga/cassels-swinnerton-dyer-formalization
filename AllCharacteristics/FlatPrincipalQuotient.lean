import AllCharacteristics.FlatCokernelCriterion
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import AllCharacteristics.RegularLocalDomain

/-!
# Flat principal quotients of flat algebras

A principal quotient of a flat algebra is flat over the coefficient ring if
the defining element is a non-zero-divisor after reduction modulo each base
ideal. This is the algebraic criterion needed on nonzero coefficient opens.
-/

open LinearMap TensorProduct
open scoped nonZeroDivisors
namespace AllCharacteristics
universe u v w

/-- A principal quotient of a flat algebra is flat if the defining element
stays a non-zero-divisor after tensoring with every base quotient. -/
theorem quotient_flat_of_tensor_nonZeroDivisors
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (p : A)
    (hp : ∀ I : Ideal R, (1 ⊗ₜ[R] p) ∈ ((R ⧸ I) ⊗[R] A)⁰) :
    Module.Flat R (A ⧸ Ideal.span {p}) := by
  let f := (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap
  let g := LinearMap.mulLeft R p
  refine flat_of_exact_of_quotient_tensor_injective g f
    Ideal.Quotient.mk_surjective ?_ ?_
  · intro a
    change Ideal.Quotient.mk (Ideal.span {p}) a = 0 ↔ ∃ b, p * b = a
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, dvd_def]
    exact exists_congr fun _ ↦ eq_comm
  · intro I
    have he : g.lTensor (R ⧸ I) = LinearMap.mulLeft R (1 ⊗ₜ[R] p : (R ⧸ I) ⊗[R] A) := by
      ext r a
      simp [g, Algebra.TensorProduct.tmul_mul_tmul]
    rw [he]
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    exact (mem_nonZeroDivisors_iff_left.mp (hp I)) x hx

/-- It suffices to test the defining element in the actual algebra quotients
by extensions of coefficient ideals. -/
theorem quotient_flat_of_nonZeroDivisors_mod_base_ideals
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (p : A)
    (hp : ∀ I : Ideal R,
      Ideal.Quotient.mk (I.map (algebraMap R A)) p ∈ (A ⧸ I.map (algebraMap R A))⁰) :
    Module.Flat R (A ⧸ Ideal.span {p}) := by
  apply quotient_flat_of_tensor_nonZeroDivisors p
  intro I
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  apply mem_nonZeroDivisors_of_injective e.symm.injective
  have he : e (Ideal.Quotient.mk (I.map (algebraMap R A)) p) = 1 ⊗ₜ[R] p :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A I p
  rw [← he, e.symm_apply_apply]
  exact hp I

/-- Two successive principal quotients of a flat algebra are flat when each
defining element stays a non-zero-divisor after reduction modulo every base
ideal.  The second condition is imposed in the first quotient. -/
theorem iterated_quotient_flat_of_nonZeroDivisors_mod_base_ideals
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (p q : A)
    (hp : ∀ I : Ideal R,
      Ideal.Quotient.mk (I.map (algebraMap R A)) p ∈ (A ⧸ I.map (algebraMap R A))⁰)
    (hq : ∀ I : Ideal R,
      Ideal.Quotient.mk
          (I.map (algebraMap R (A ⧸ Ideal.span {p})))
          (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
        ((A ⧸ Ideal.span {p}) ⧸
          I.map (algebraMap R (A ⧸ Ideal.span {p})))⁰) :
    Module.Flat R
      ((A ⧸ Ideal.span {p}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) q}) := by
  let _ : Module.Flat R (A ⧸ Ideal.span {p}) :=
    quotient_flat_of_nonZeroDivisors_mod_base_ideals p hp
  exact quotient_flat_of_nonZeroDivisors_mod_base_ideals
    (Ideal.Quotient.mk (Ideal.span {p}) q) hq

/-- The quotient by the two-element ideal `(p, q)` is flat when `p` and then
the image of `q` satisfy the fibrewise non-zero-divisor criterion. -/
theorem quotient_flat_of_two_nonZeroDivisors_mod_base_ideals
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (p q : A)
    (hp : ∀ I : Ideal R,
      Ideal.Quotient.mk (I.map (algebraMap R A)) p ∈ (A ⧸ I.map (algebraMap R A))⁰)
    (hq : ∀ I : Ideal R,
      Ideal.Quotient.mk
          (I.map (algebraMap R (A ⧸ Ideal.span {p})))
          (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
        ((A ⧸ Ideal.span {p}) ⧸
          I.map (algebraMap R (A ⧸ Ideal.span {p})))⁰) :
    Module.Flat R (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  let hflat : Module.Flat R
      ((A ⧸ Ideal.span {p}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) q}) :=
    iterated_quotient_flat_of_nonZeroDivisors_mod_base_ideals p q hp hq
  have hq' : Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) q} =
      (Ideal.span {q}).map (Ideal.Quotient.mk (Ideal.span {p})) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hq'] at hflat
  let _ : Module.Flat R ((A ⧸ Ideal.span {p}) ⧸
      (Ideal.span {q}).map (Ideal.Quotient.mkₐ R (Ideal.span {p}))) := by
    exact hflat
  exact Module.Flat.of_linearEquiv
    (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {p})
      (Ideal.span {q})).toLinearEquiv.symm

/-- A pair is fibrewise regular over a ring map when the first coordinate and
then the second modulo the first remain non-zero-divisors after every base
ideal reduction. -/
def IsFibrewiseRegularPair
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A) : Prop :=
  (∀ I : Ideal R,
    Ideal.Quotient.mk (I.map φ) p ∈ (A ⧸ I.map φ)⁰) ∧
  (∀ I : Ideal R,
    Ideal.Quotient.mk
        (I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))
        (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
      ((A ⧸ Ideal.span {p}) ⧸
      I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰)

/-- Reducing a fibrewise regular pair modulo a coefficient ideal produces a
weakly regular sequence in the actual reduced coordinate ring.  The second
coordinate uses the canonical equivalence which swaps the base reduction and
the first principal quotient. -/
theorem IsFibrewiseRegularPair.weaklyRegular_quotient_map
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) (I : Ideal R) :
    RingTheory.Sequence.IsWeaklyRegular (A ⧸ I.map φ)
      [Ideal.Quotient.mk (I.map φ) p, Ideal.Quotient.mk (I.map φ) q] := by
  let J := I.map φ
  let B := A ⧸ J
  let p' : B := Ideal.Quotient.mk J p
  let q' : B := Ideal.Quotient.mk J q
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  constructor
  · exact IsRegular.isSMulRegular
      (isRegular_iff_mem_nonZeroDivisors.mpr (by
        simpa [J] using hregular.1 I))
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    let e₀ := DoubleQuot.quotQuotEquivComm (I.map φ) (Ideal.span {p})
    have hspan : (Ideal.span {p}).map (Ideal.Quotient.mk (I.map φ)) =
        Ideal.span {Ideal.Quotient.mk (I.map φ) p} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hmap : I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) =
        (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})) := by
      exact (Ideal.map_map φ (Ideal.Quotient.mk (Ideal.span {p}))).symm
    let e₁ : B ⧸ Ideal.span {p'} ≃+*
        B ⧸ (Ideal.span {p}).map (Ideal.Quotient.mk (I.map φ)) :=
      Ideal.quotEquivOfEq hspan.symm
    let e₂ : ((A ⧸ Ideal.span {p}) ⧸
        (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) ≃+*
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)) :=
      Ideal.quotEquivOfEq hmap.symm
    let e : B ⧸ Ideal.span {p'} ≃+*
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)) :=
      e₁.trans (e₀.trans e₂)
    have hq := hregular.2 I
    have heq : e (Ideal.Quotient.mk (Ideal.span {p'}) q') =
        Ideal.Quotient.mk
          (I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))
          (Ideal.Quotient.mk (Ideal.span {p}) q) := by
      dsimp [e, e₁, e₂, e₀, B, J, p', q']
      have hcomp : algebraMap A ((A ⧸ Ideal.span {p}) ⧸
          (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) q =
          algebraMap (A ⧸ Ideal.span {p}) ((A ⧸ Ideal.span {p}) ⧸
            (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})))
            (Ideal.Quotient.mk (Ideal.span {p}) q) := by
        exact IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {p})
          ((A ⧸ Ideal.span {p}) ⧸
            (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) q
      rw [hcomp]
      change (Ideal.quotEquivOfEq hmap.symm)
        (Ideal.Quotient.mk ((I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})))
          (Ideal.Quotient.mk (Ideal.span {p}) q)) = _
      rw [Ideal.quotEquivOfEq_mk]
    have hq' : Ideal.Quotient.mk (Ideal.span {p'}) q' ∈
        (B ⧸ Ideal.span {p'})⁰ := by
      have hey : e (Ideal.Quotient.mk (Ideal.span {p'}) q') ∈
          ((A ⧸ Ideal.span {p}) ⧸
            I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰ := by
        rw [heq]
        exact hq
      rw [← MulEquivClass.map_nonZeroDivisors e] at hey
      rcases hey with ⟨z, hz, hz_eq⟩
      have hzx : z = Ideal.Quotient.mk (Ideal.span {p'}) q' := e.injective hz_eq
      simpa [hzx] using hz
    let ee : QuotSMulTop p' B ≃ₗ[B] B ⧸ Ideal.span {p'} :=
      Submodule.quotEquivOfEq _ _ (by
        simpa using
          (Submodule.ideal_span_singleton_smul p' (⊤ : Submodule B B)).symm)
    rw [ee.isSMulRegular_congr]
    rw [← isSMulRegular_algebraMap_iff
      (A := B ⧸ Ideal.span {p'}) (M := B ⧸ Ideal.span {p'})]
    exact IsRegular.isSMulRegular
      (isRegular_iff_mem_nonZeroDivisors.mpr hq')

/-- The fibrewise regularity condition is equivalently witnessed by weakly
regular pairs in every actual base-ideal quotient.  This converse to
`IsFibrewiseRegularPair.weaklyRegular_quotient_map` lets a geometric
regular-sequence calculation feed directly into the flatness criterion. -/
theorem isFibrewiseRegularPair_of_weaklyRegular_quotient_maps
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A)
    (hweak : ∀ I : Ideal R,
      RingTheory.Sequence.IsWeaklyRegular (A ⧸ I.map φ)
        [Ideal.Quotient.mk (I.map φ) p, Ideal.Quotient.mk (I.map φ) q]) :
    IsFibrewiseRegularPair φ p q := by
  constructor
  · intro I
    have hseq := hweak I
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hseq
    exact isRegular_iff_mem_nonZeroDivisors.mp
      (isLeftRegular_iff_isRegular.mp hseq.1.isLeftRegular)
  · intro I
    let J := I.map φ
    let B := A ⧸ J
    let p' : B := Ideal.Quotient.mk J p
    let q' : B := Ideal.Quotient.mk J q
    have hseq : RingTheory.Sequence.IsWeaklyRegular B [p', q'] := by
      simpa [B, J, p', q'] using hweak I
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hseq
    let ee : QuotSMulTop p' B ≃ₗ[B] B ⧸ Ideal.span {p'} :=
      Submodule.quotEquivOfEq _ _ (by
        simpa using
          (Submodule.ideal_span_singleton_smul p' (⊤ : Submodule B B)).symm)
    have hqB : Ideal.Quotient.mk (Ideal.span {p'}) q' ∈
        (B ⧸ Ideal.span {p'})⁰ := by
      have hq : IsSMulRegular (B ⧸ Ideal.span {p'}) q' :=
        (ee.isSMulRegular_congr q').mp hseq.2
      have hq' : IsSMulRegular (B ⧸ Ideal.span {p'})
          (algebraMap B (B ⧸ Ideal.span {p'}) q') :=
        (isSMulRegular_algebraMap_iff
          (A := B ⧸ Ideal.span {p'}) (M := B ⧸ Ideal.span {p'})).mpr hq
      simpa only [Ideal.Quotient.algebraMap_eq] using
        isRegular_iff_mem_nonZeroDivisors.mp
          (isLeftRegular_iff_isRegular.mp hq'.isLeftRegular)
    let e₀ := DoubleQuot.quotQuotEquivComm (I.map φ) (Ideal.span {p})
    have hspan : (Ideal.span {p}).map (Ideal.Quotient.mk (I.map φ)) =
        Ideal.span {Ideal.Quotient.mk (I.map φ) p} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hmap : I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) =
        (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})) := by
      exact (Ideal.map_map φ (Ideal.Quotient.mk (Ideal.span {p}))).symm
    let e₁ : B ⧸ Ideal.span {p'} ≃+*
        B ⧸ (Ideal.span {p}).map (Ideal.Quotient.mk (I.map φ)) :=
      Ideal.quotEquivOfEq hspan.symm
    let e₂ : ((A ⧸ Ideal.span {p}) ⧸
        (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) ≃+*
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)) :=
      Ideal.quotEquivOfEq hmap.symm
    let e : B ⧸ Ideal.span {p'} ≃+*
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)) :=
      e₁.trans (e₀.trans e₂)
    have heq : e (Ideal.Quotient.mk (Ideal.span {p'}) q') =
        Ideal.Quotient.mk
          (I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))
          (Ideal.Quotient.mk (Ideal.span {p}) q) := by
      dsimp [e, e₁, e₂, e₀, B, J, p', q']
      have hcomp : algebraMap A ((A ⧸ Ideal.span {p}) ⧸
          (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) q =
          algebraMap (A ⧸ Ideal.span {p}) ((A ⧸ Ideal.span {p}) ⧸
            (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})))
            (Ideal.Quotient.mk (Ideal.span {p}) q) := by
        exact IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {p})
          ((A ⧸ Ideal.span {p}) ⧸
            (I.map φ).map (Ideal.Quotient.mk (Ideal.span {p}))) q
      rw [hcomp]
      change (Ideal.quotEquivOfEq hmap.symm)
        (Ideal.Quotient.mk ((I.map φ).map (Ideal.Quotient.mk (Ideal.span {p})))
          (Ideal.Quotient.mk (Ideal.span {p}) q)) = _
      rw [Ideal.quotEquivOfEq_mk]
    have hqE : e (Ideal.Quotient.mk (Ideal.span {p'}) q') ∈
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰ := by
      rw [← MulEquivClass.map_nonZeroDivisors e]
      exact ⟨Ideal.Quotient.mk (Ideal.span {p'}) q', hqB, rfl⟩
    rwa [heq] at hqE

/-- A fibrewise regular pair is precisely a weakly regular pair after every
actual reduction of the base ring. -/
theorem isFibrewiseRegularPair_iff_weaklyRegular_quotient_maps
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A) :
    IsFibrewiseRegularPair φ p q ↔
      ∀ I : Ideal R,
        RingTheory.Sequence.IsWeaklyRegular (A ⧸ I.map φ)
          [Ideal.Quotient.mk (I.map φ) p, Ideal.Quotient.mk (I.map φ) q] := by
  constructor
  · intro hregular I
    exact hregular.weaklyRegular_quotient_map φ p q I
  · exact isFibrewiseRegularPair_of_weaklyRegular_quotient_maps φ p q

/-- The weak regular sequence in a reduced coordinate ring remains weakly
regular after localizing that reduced ring. -/
theorem IsFibrewiseRegularPair.weaklyRegular_localization_quotient_map
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S]
    (φ : R →+* A) (p q : A) (I : Ideal R)
    [Algebra (A ⧸ I.map φ) S] (T : Submonoid (A ⧸ I.map φ)) [IsLocalization T S]
    (hregular : IsFibrewiseRegularPair φ p q) :
    RingTheory.Sequence.IsWeaklyRegular S
      [algebraMap (A ⧸ I.map φ) S (Ideal.Quotient.mk (I.map φ) p),
        algebraMap (A ⧸ I.map φ) S (Ideal.Quotient.mk (I.map φ) q)] := by
  simpa using RingTheory.Sequence.IsWeaklyRegular.of_isLocalization S T
    (hregular.weaklyRegular_quotient_map φ p q I)

/-- A fibrewise regular pair stays weakly regular on every residue-field
fibre.  The fibre is the localization of the coordinate ring reduced modulo
the base prime, and regular sequences persist under that localization. -/
theorem IsFibrewiseRegularPair.weaklyRegular_fiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair (algebraMap R S) a b) :
    RingTheory.Sequence.IsWeaklyRegular (R := P.asIdeal.Fiber S) (P.asIdeal.Fiber S)
      ([(1 ⊗ₜ[R] a : P.asIdeal.Fiber S), (1 ⊗ₜ[R] b)] : List (P.asIdeal.Fiber S)) := by
  let I : Ideal R := P.asIdeal
  let Q := R ⧸ I
  let B := S ⧸ I.map (algebraMap R S)
  let B₀ := Q ⊗[R] S
  let K := I.ResidueField
  let T := K ⊗[Q] B₀
  let F := I.Fiber S
  let eB : B ≃ₐ[Q] B₀ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  let eF : T ≃ₐ[K] F := Algebra.TensorProduct.cancelBaseChange R Q K K S
  let M₀ : Submonoid B₀ := Algebra.algebraMapSubmonoid B₀ (nonZeroDivisors Q)
  let M : Submonoid B := M₀.map eB.symm.toRingEquiv.toMonoidHom
  letI : Algebra B₀ T := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization M₀ T := by
    change IsLocalization (Algebra.algebraMapSubmonoid B₀ (nonZeroDivisors Q)) (K ⊗[Q] B₀)
    infer_instance
  letI : Algebra B₀ F :=
    ((eF.toRingEquiv.toRingHom.comp (algebraMap B₀ T)).toAlgebra)
  let hlocF : IsLocalization M₀ F :=
    @IsLocalization.isLocalization_of_algEquiv B₀ _ M₀ T _ _ F _ _ _
      ({ __ := eF.toRingEquiv, commutes' := by intro r; rfl } : T ≃ₐ[B₀] F)
  letI : IsLocalization M₀ F := hlocF
  letI : Algebra B F :=
    ((algebraMap B₀ F).comp eB.toRingEquiv.toRingHom).toAlgebra
  letI : IsLocalization M F :=
    IsLocalization.of_ringEquiv_left (M₁ := M₀) (M₂ := M) eB.toRingEquiv
      (by ext x; simp [M]) (by intro r; rfl)
  have hseq : RingTheory.Sequence.IsWeaklyRegular (R := B) B
      ([Ideal.Quotient.mk (I.map (algebraMap R S)) a,
        Ideal.Quotient.mk (I.map (algebraMap R S)) b] : List B) :=
    hregular.weaklyRegular_quotient_map (algebraMap R S) a b I
  have hseqF := RingTheory.Sequence.IsWeaklyRegular.of_isLocalization F M hseq
  have hmap (x : S) :
      algebraMap B F (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
        (1 ⊗ₜ[R] x : F) := by
    change eF (Algebra.TensorProduct.includeRight
      (eB (Ideal.Quotient.mk (I.map (algebraMap R S)) x))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change eF (1 ⊗ₜ[Q] (1 ⊗ₜ[R] x)) = _
    simp [eF, F, T, K, B₀, Q]
  simpa only [List.map_cons, List.map_nil, hmap] using hseqF

/-- Over a field, the first member of a fibrewise regular pair is already a
non-zero-divisor in the ambient ring. -/
theorem IsFibrewiseRegularPair.first_mem_nonZeroDivisors_of_field
    {K : Type u} {A : Type v} [Field K] [CommRing A]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    p ∈ A⁰ := by
  have hp := hregular.1 (⊥ : Ideal K)
  let e : A ⧸ (Ideal.map φ (⊥ : Ideal K)) ≃+* A :=
    (Ideal.quotEquivOfEq (Ideal.map_bot : Ideal.map φ (⊥ : Ideal K) = ⊥)).trans
      (RingEquiv.quotientBot A)
  have hp' : e (Ideal.Quotient.mk (Ideal.map φ (⊥ : Ideal K)) p) ∈ A⁰ := by
    rw [← MulEquivClass.map_nonZeroDivisors e]
    exact ⟨Ideal.Quotient.mk (Ideal.map φ (⊥ : Ideal K)) p, hp, rfl⟩
  simpa [e] using hp'

/-- Over a field, the second member of a fibrewise regular pair is a
non-zero-divisor after quotienting by the first member. -/
theorem IsFibrewiseRegularPair.second_mem_nonZeroDivisors_of_field
    {K : Type u} {A : Type v} [Field K] [CommRing A]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    Ideal.Quotient.mk (Ideal.span {p}) q ∈ (A ⧸ Ideal.span {p})⁰ := by
  let S := A ⧸ Ideal.span {p}
  have hq := hregular.2 (⊥ : Ideal K)
  let e : S ⧸ (Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)
      (⊥ : Ideal K)) ≃+* S :=
    (Ideal.quotEquivOfEq (Ideal.map_bot :
      Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) (⊥ : Ideal K) = ⊥)).trans
      (RingEquiv.quotientBot S)
  have hq' : e (Ideal.Quotient.mk
      (Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) (⊥ : Ideal K))
      (Ideal.Quotient.mk (Ideal.span {p}) q)) ∈ S⁰ := by
    rw [← MulEquivClass.map_nonZeroDivisors e]
    exact ⟨Ideal.Quotient.mk
      (Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) (⊥ : Ideal K))
      (Ideal.Quotient.mk (Ideal.span {p}) q), hq, rfl⟩
  simpa [S, e] using hq'

/-- Over a field, fibrewise regularity is exactly ordinary regularity of the
two successive coordinate equations. The top ideal of the field produces a
subsingleton quotient, so it introduces no further condition. -/
theorem isFibrewiseRegularPair_iff_of_field
    {K : Type u} {A : Type v} [Field K] [CommRing A]
    (φ : K →+* A) (p q : A) :
    IsFibrewiseRegularPair φ p q ↔
      p ∈ A⁰ ∧ Ideal.Quotient.mk (Ideal.span {p}) q ∈ (A ⧸ Ideal.span {p})⁰ := by
  constructor
  · intro hregular
    exact ⟨hregular.first_mem_nonZeroDivisors_of_field φ p q,
      hregular.second_mem_nonZeroDivisors_of_field φ p q⟩
  · rintro ⟨hp, hq⟩
    constructor
    · intro I
      rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
      · subst I
        let e : A ⧸ (Ideal.map φ (⊥ : Ideal K)) ≃+* A :=
          (Ideal.quotEquivOfEq (Ideal.map_bot : Ideal.map φ (⊥ : Ideal K) = ⊥)).trans
            (RingEquiv.quotientBot A)
        have hp' : e.symm p ∈ (A ⧸ Ideal.map φ (⊥ : Ideal K))⁰ := by
          rw [← MulEquivClass.map_nonZeroDivisors e.symm]
          exact ⟨p, hp, rfl⟩
        simpa [e] using hp'
      · subst I
        let : Subsingleton (A ⧸ Ideal.map φ (⊤ : Ideal K)) :=
          Ideal.Quotient.subsingleton_iff.mpr (Ideal.map_top φ)
        rw [mem_nonZeroDivisors_iff]
        exact ⟨fun x _ ↦ Subsingleton.elim _ _, fun x _ ↦ Subsingleton.elim _ _⟩
    · intro I
      rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
      · subst I
        let S := A ⧸ Ideal.span {p}
        let e : S ⧸ (Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)
            (⊥ : Ideal K)) ≃+* S :=
          (Ideal.quotEquivOfEq (Ideal.map_bot :
            Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) (⊥ : Ideal K) = ⊥)).trans
            (RingEquiv.quotientBot S)
        have hq' : e.symm (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
            (S ⧸ Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)
              (⊥ : Ideal K))⁰ := by
          rw [← MulEquivClass.map_nonZeroDivisors e.symm]
          exact ⟨Ideal.Quotient.mk (Ideal.span {p}) q, hq, rfl⟩
        simpa [S, e] using hq'
      · subst I
        let S := A ⧸ Ideal.span {p}
        let : Subsingleton (S ⧸ Ideal.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ)
            (⊤ : Ideal K)) :=
          Ideal.Quotient.subsingleton_iff.mpr
            (Ideal.map_top ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))
        rw [mem_nonZeroDivisors_iff]
        exact ⟨fun x _ ↦ Subsingleton.elim _ _, fun x _ ↦ Subsingleton.elim _ _⟩

/-- In a domain, a nonzero first equation and a second equation outside its
prime principal ideal form a fibrewise regular pair over a field.  This is
the direct algebraic bridge used by the selected-prime branches of Voisin's
construction: primality supplies the quotient domain, so no separate
associated-prime hypothesis is needed. -/
theorem isFibrewiseRegularPair_of_domain_of_prime_span_of_not_mem
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [IsDomain A] (p q : A) (hp0 : p ≠ 0)
    (hp : (Ideal.span ({p} : Set A)).IsPrime)
    (hq : q ∉ Ideal.span ({p} : Set A)) :
    IsFibrewiseRegularPair (algebraMap K A) p q := by
  rw [isFibrewiseRegularPair_iff_of_field]
  refine ⟨mem_nonZeroDivisors_iff_ne_zero.mpr hp0, ?_⟩
  letI : IsDomain (A ⧸ Ideal.span ({p} : Set A)) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hp
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  apply hq
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- Over a field, regularity of a pair can be checked locally after quotienting
by its first member.  This is the local-to-global form used when a geometric
argument shows that the second equation is a non-zero-divisor at every point
of its zero curve. -/
theorem isFibrewiseRegularPair_of_field_of_first_nonZeroDivisor_of_local_second_nonZeroDivisors
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (p q : A) (hp : p ∈ A⁰)
    (hlocal : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
        (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
          (Localization.AtPrime P)⁰) :
    IsFibrewiseRegularPair (algebraMap K A) p q := by
  rw [isFibrewiseRegularPair_iff_of_field]
  constructor
  · exact hp
  · rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      apply Module.eq_zero_of_localization_maximal _
        (fun P _ => Algebra.linearMap (A ⧸ Ideal.span {p})
          (Localization.AtPrime P)) x
      intro P _
      apply (mem_nonZeroDivisors_iff_left.mp (hlocal P))
      change algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
          (Ideal.Quotient.mk (Ideal.span {p}) q) *
          algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P) x = 0
      rw [← map_mul, hx, map_zero]
    · intro x hx
      apply Module.eq_zero_of_localization_maximal _
        (fun P _ => Algebra.linearMap (A ⧸ Ideal.span {p})
          (Localization.AtPrime P)) x
      intro P _
      apply (mem_nonZeroDivisors_iff_right.mp (hlocal P))
      change algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P) x *
          algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
            (Ideal.Quotient.mk (Ideal.span {p}) q) = 0
      rw [← map_mul, hx, map_zero]

/-- The preceding local criterion specializes to a domain once the first
equation is nonzero. -/
theorem isFibrewiseRegularPair_of_field_of_domain_of_local_second_nonZeroDivisors
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A] [IsDomain A]
    (p q : A) (hp : p ≠ 0)
    (hlocal : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
        (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
          (Localization.AtPrime P)⁰) :
    IsFibrewiseRegularPair (algebraMap K A) p q := by
  apply isFibrewiseRegularPair_of_field_of_first_nonZeroDivisor_of_local_second_nonZeroDivisors
    p q
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hp
  · exact hlocal

/-- A cotangent-space parameter for the quotient by a nonzero first equation
is a local non-zero-divisor on a regular local chart.  Therefore these local
conditions on every point of the zero curve give a fibrewise regular pair. -/
theorem isFibrewiseRegularPair_of_field_of_first_nonZeroDivisor_of_local_regular_second
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (p q : A) (hp : p ∈ A⁰)
    (hregular : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime P))
    (hsquare : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      Ideal.Quotient.mk (Ideal.span {p}) q ∈ P →
      algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
        (Ideal.Quotient.mk (Ideal.span {p}) q) ∉
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 2) :
    IsFibrewiseRegularPair (algebraMap K A) p q := by
  apply isFibrewiseRegularPair_of_field_of_first_nonZeroDivisor_of_local_second_nonZeroDivisors
    p q hp
  intro P _
  by_cases hqP : Ideal.Quotient.mk (Ideal.span {p}) q ∈ P
  · letI : IsRegularLocalRing (Localization.AtPrime P) := hregular P
    letI : IsDomain (Localization.AtPrime P) :=
      isDomain_of_regularLocalRing (Localization.AtPrime P)
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    apply hsquare P hqP
    rw [hzero]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 2).zero_mem
  · exact (IsLocalization.map_units (Localization.AtPrime P)
      (⟨Ideal.Quotient.mk (Ideal.span {p}) q, hqP⟩ : P.primeCompl)).mem_nonZeroDivisors

/-- The cotangent-parameter criterion in its domain form. -/
theorem isFibrewiseRegularPair_of_field_of_domain_of_local_regular_second
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A] [IsDomain A]
    (p q : A) (hp : p ≠ 0)
    (hregular : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime P))
    (hsquare : ∀ (P : Ideal (A ⧸ Ideal.span {p})) [P.IsMaximal],
      Ideal.Quotient.mk (Ideal.span {p}) q ∈ P →
      algebraMap (A ⧸ Ideal.span {p}) (Localization.AtPrime P)
        (Ideal.Quotient.mk (Ideal.span {p}) q) ∉
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 2) :
    IsFibrewiseRegularPair (algebraMap K A) p q := by
  apply isFibrewiseRegularPair_of_field_of_first_nonZeroDivisor_of_local_regular_second
    p q
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hp
  · exact hregular
  · exact hsquare

/-- A fibrewise regular pair on the original affine family induces the same
condition on every residue-field fibre. -/
theorem IsFibrewiseRegularPair.fiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair (algebraMap R S) a b) :
    IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b) := by
  rw [isFibrewiseRegularPair_iff_of_field]
  have hseq := hregular.weaklyRegular_fiber P a b
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hseq
  constructor
  · exact isRegular_iff_mem_nonZeroDivisors.mp
      (isLeftRegular_iff_isRegular.mp hseq.1.isLeftRegular)
  · let e : QuotSMulTop (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (P.asIdeal.Fiber S) ≃ₗ[P.asIdeal.Fiber S]
        (P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _) :=
      Submodule.quotEquivOfEq _ _ (by
        simpa using
          (Submodule.ideal_span_singleton_smul (1 ⊗ₜ[R] a : P.asIdeal.Fiber S)
            (⊤ : Submodule (P.asIdeal.Fiber S) (P.asIdeal.Fiber S))).symm)
    have hb : IsSMulRegular
        ((P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _))
        (1 ⊗ₜ[R] b : P.asIdeal.Fiber S) :=
      (e.isSMulRegular_congr (1 ⊗ₜ[R] b : P.asIdeal.Fiber S)).mp hseq.2
    have hb' : IsSMulRegular
        ((P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _))
        (algebraMap (P.asIdeal.Fiber S)
          ((P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _))
          (1 ⊗ₜ[R] b : P.asIdeal.Fiber S)) :=
      (isSMulRegular_algebraMap_iff
        (A := (P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _))
        (M := (P.asIdeal.Fiber S) ⧸ Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set _))).mpr hb
    simpa only [Ideal.Quotient.algebraMap_eq] using
      isRegular_iff_mem_nonZeroDivisors.mp
        (isLeftRegular_iff_isRegular.mp hb'.isLeftRegular)

/-- Over a field, a fibrewise regular pair is a weakly regular sequence in
the ambient ring.  This translates the quotient-ring non-zero-divisor form
of `IsFibrewiseRegularPair` into the regular-sequence form preserved by
localization. -/
theorem IsFibrewiseRegularPair.weaklyRegular_of_field
    {K : Type u} {A : Type v} [Field K] [CommRing A]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    RingTheory.Sequence.IsWeaklyRegular A [p, q] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  constructor
  · exact IsRegular.isSMulRegular
      (isRegular_iff_mem_nonZeroDivisors.mpr
        (hregular.first_mem_nonZeroDivisors_of_field φ p q))
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    let e : QuotSMulTop p A ≃ₗ[A] A ⧸ Ideal.span {p} :=
      Submodule.quotEquivOfEq _ _ (by
        simpa using
          (Submodule.ideal_span_singleton_smul p (⊤ : Submodule A A)).symm)
    rw [e.isSMulRegular_congr]
    rw [← isSMulRegular_algebraMap_iff
      (A := A ⧸ Ideal.span {p}) (M := A ⧸ Ideal.span {p})]
    exact IsRegular.isSMulRegular
      (isRegular_iff_mem_nonZeroDivisors.mpr
        (hregular.second_mem_nonZeroDivisors_of_field φ p q))

/-- A regular pair on an affine scheme over a field remains fibrewise regular
after arbitrary base change of the coefficient algebra.  In particular, this
supplies the all-ideal regularity needed for a pencil over an affine parameter
chart from a regular pair on the original field-valued chart. -/
theorem isFibrewiseRegularPair_tensorProduct_includeLeft_of_field
    {K : Type u} {R : Type v} {B : Type w}
    [Field K] [CommRing R] [Algebra K R] [CommRing B] [Algebra K B]
    (p q : B) (hregular : IsFibrewiseRegularPair (algebraMap K B) p q) :
    IsFibrewiseRegularPair (algebraMap R (R ⊗[K] B))
      (1 ⊗ₜ[K] p) (1 ⊗ₜ[K] q) := by
  rw [isFibrewiseRegularPair_iff_weaklyRegular_quotient_maps]
  intro I
  let T' := B ⊗[K] (R ⧸ I)
  let T := (R ⧸ I) ⊗[K] B
  let eT : T' ≃+* T := (Algebra.TensorProduct.comm K B (R ⧸ I)).toRingEquiv
  let eQ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (R ⊗[K] B) I
  let eC := Algebra.TensorProduct.cancelBaseChange K R (R ⧸ I) (R ⧸ I) B
  have hseqB : RingTheory.Sequence.IsWeaklyRegular B [p, q] :=
    hregular.weaklyRegular_of_field (algebraMap K B) p q
  haveI : Module.Flat B T' := by
    dsimp [T']
    infer_instance
  have hseqT' : RingTheory.Sequence.IsWeaklyRegular T'
      [algebraMap B T' p, algebraMap B T' q] :=
    hseqB.of_flat
  have hseqT : RingTheory.Sequence.IsWeaklyRegular T
      [(1 ⊗ₜ[K] p : T), (1 ⊗ₜ[K] q : T)] := by
    apply (eT.toAddEquiv.isWeaklyRegular_congr (as :=
      [algebraMap B T' p, algebraMap B T' q]) (bs :=
      [(1 ⊗ₜ[K] p : T), (1 ⊗ₜ[K] q : T)]) ?_).mp hseqT'
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)
    · intro x
      change eT (algebraMap B T' p * x) = (1 ⊗ₜ[K] p : T) * eT x
      rw [map_mul]
      rfl
    · intro x
      change eT (algebraMap B T' q * x) = (1 ⊗ₜ[K] q : T) * eT x
      rw [map_mul]
      rfl
  let e : (R ⊗[K] B ⧸ I.map (algebraMap R (R ⊗[K] B))) ≃+* T :=
    eQ.toRingEquiv.trans eC.toRingEquiv
  apply (e.symm.toAddEquiv.isWeaklyRegular_congr (as :=
    [(1 ⊗ₜ[K] p : T), (1 ⊗ₜ[K] q : T)]) (bs :=
    [Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B))) (1 ⊗ₜ[K] p),
      Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B)))
        (1 ⊗ₜ[K] q)]) ?_).mp hseqT
  have ep : e.symm (1 ⊗ₜ[K] p : T) =
      Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B))) (1 ⊗ₜ[K] p) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (1 ⊗ₜ[K] p : T) = eC (eQ
      (Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B)))
        (1 ⊗ₜ[K] p)))
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (1 ⊗ₜ[K] p : T) =
      Algebra.TensorProduct.cancelBaseChange K R (R ⧸ I) (R ⧸ I) B
        (1 ⊗ₜ[R] (1 ⊗ₜ[K] p))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp
  have eq : e.symm (1 ⊗ₜ[K] q : T) =
      Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B))) (1 ⊗ₜ[K] q) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (1 ⊗ₜ[K] q : T) = eC (eQ
      (Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B)))
        (1 ⊗ₜ[K] q)))
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (1 ⊗ₜ[K] q : T) =
      Algebra.TensorProduct.cancelBaseChange K R (R ⧸ I) (R ⧸ I) B
        (1 ⊗ₜ[R] (1 ⊗ₜ[K] q))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)
  · intro x
    change e.symm ((1 ⊗ₜ[K] p : T) * x) =
      Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B)))
        (1 ⊗ₜ[K] p) * e.symm x
    rw [map_mul, ep]
  · intro x
    change e.symm ((1 ⊗ₜ[K] q : T) * x) =
      Ideal.Quotient.mk (I.map (algebraMap R (R ⊗[K] B)))
        (1 ⊗ₜ[K] q) * e.symm x
    rw [map_mul, eq]

/-- The weak regular sequence attached to a fibrewise regular pair over a
field remains weakly regular after localization.  This is the local-ring
form needed at common zeros on a smooth surface fibre. -/
theorem IsFibrewiseRegularPair.weaklyRegular_localization_of_field
    {K : Type u} {A : Type v} {S : Type w} [Field K] [CommRing A] [CommRing S]
    [Algebra A S] (T : Submonoid A) [IsLocalization T S]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    RingTheory.Sequence.IsWeaklyRegular S
      [algebraMap A S p, algebraMap A S q] := by
  simpa using RingTheory.Sequence.IsWeaklyRegular.of_isLocalization S T
    (hregular.weaklyRegular_of_field φ p q)

/-- At a localization of a field fibre, a fibrewise regular pair gives the
two successive non-zero-divisor statements in the localized coordinate ring.
This is the form consumed by the local dimension calculation for a pencil
zero locus. -/
theorem IsFibrewiseRegularPair.local_nonZeroDivisors_of_field_of_isLocalization
    {K : Type u} {A : Type v} {S : Type w} [Field K] [CommRing A] [CommRing S]
    [Algebra A S] (T : Submonoid A) [IsLocalization T S]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    algebraMap A S p ∈ S⁰ ∧
      Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
        (S ⧸ Ideal.span {algebraMap A S p})⁰ := by
  have hseq : RingTheory.Sequence.IsWeaklyRegular S
      [algebraMap A S p, algebraMap A S q] :=
    hregular.weaklyRegular_localization_of_field T φ p q
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hseq
  constructor
  · exact isRegular_iff_mem_nonZeroDivisors.mp
      (isLeftRegular_iff_isRegular.mp hseq.1.isLeftRegular)
  · let e : QuotSMulTop (algebraMap A S p) S ≃ₗ[S]
        S ⧸ Ideal.span {algebraMap A S p} :=
      Submodule.quotEquivOfEq _ _ (by
        simpa using
          (Submodule.ideal_span_singleton_smul (algebraMap A S p)
            (⊤ : Submodule S S)).symm)
    have hq : IsSMulRegular (S ⧸ Ideal.span {algebraMap A S p})
        (algebraMap A S q) :=
      (e.isSMulRegular_congr (algebraMap A S q)).mp hseq.2
    have hq' : IsSMulRegular (S ⧸ Ideal.span {algebraMap A S p})
        (algebraMap S (S ⧸ Ideal.span {algebraMap A S p}) (algebraMap A S q)) :=
      (isSMulRegular_algebraMap_iff
        (A := S ⧸ Ideal.span {algebraMap A S p})
        (M := S ⧸ Ideal.span {algebraMap A S p})).mpr hq
    simpa only [Ideal.Quotient.algebraMap_eq] using
      isRegular_iff_mem_nonZeroDivisors.mp
        (isLeftRegular_iff_isRegular.mp hq'.isLeftRegular)

/-- Replacing the second member of a fibrewise regular pair by itself plus a
multiple of the first member preserves fibrewise regularity.  This is the
elementary coordinate change used when normalizing a rank-two pencil on an
affine parameter chart. -/
theorem IsFibrewiseRegularPair.second_add_first_mul
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q r : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    IsFibrewiseRegularPair φ p (q + p * r) := by
  refine ⟨hregular.1, ?_⟩
  have hpzero : Ideal.Quotient.mk (Ideal.span {p}) p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton p))
  intro I
  simpa only [map_add, map_mul, map_zero, hpzero, zero_mul, zero_add, add_zero] using
    hregular.2 I

/-- Multiplying the second member of a fibrewise regular pair by a unit
preserves fibrewise regularity.  Together with
`IsFibrewiseRegularPair.second_add_first_mul`, this handles the affine
coordinate changes used to normalize a rank-two pencil. -/
theorem IsFibrewiseRegularPair.second_mul_unit
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A) (u : Aˣ)
    (hregular : IsFibrewiseRegularPair φ p q) :
    IsFibrewiseRegularPair φ p (q * u) := by
  refine ⟨hregular.1, ?_⟩
  intro I
  let ψ : A →+* (A ⧸ Ideal.span {p}) ⧸
      I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ) :=
    (Ideal.Quotient.mk
      (I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))).comp
        (Ideal.Quotient.mk (Ideal.span {p}))
  have hu : ψ u ∈
      ((A ⧸ Ideal.span {p}) ⧸
        I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰ :=
    (ψ.isUnit_map u.isUnit).mem_nonZeroDivisors
  change ψ (q * u) ∈
    ((A ⧸ Ideal.span {p}) ⧸
      I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰
  rw [map_mul]
  exact (nonZeroDivisors _).mul_mem (hregular.2 I) hu

/- If the first coordinate is a unit, the first principal quotient is the
  zero ring, so the fibrewise regular-pair condition is automatic. -/
theorem isFibrewiseRegularPair_of_first_isUnit
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q : A) (hp : IsUnit p) :
    IsFibrewiseRegularPair φ p q := by
  constructor
  · intro I
    exact (hp.map (Ideal.Quotient.mk (I.map φ))).mem_nonZeroDivisors
  · intro I
    have htop : Ideal.span ({p} : Set A) = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hp
    let S : Type v := A ⧸ Ideal.span ({p} : Set A)
    let J : Ideal S := I.map ((Ideal.Quotient.mk (Ideal.span ({p} : Set A))).comp φ)
    letI : Subsingleton S :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    letI : Subsingleton (S ⧸ J) := ⟨fun _ _ => Subsingleton.elim _ _⟩
    change (Ideal.Quotient.mk J (Ideal.Quotient.mk (Ideal.span ({p} : Set A)) q)) ∈
      (S ⧸ J)⁰
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x _ ↦ Subsingleton.elim _ _, fun x _ ↦ Subsingleton.elim _ _⟩

/- On the overlap where a normalized projective coordinate is the
   distinguished coordinate, the first member is literally one.  Such a
   pair is fibrewise regular independently of the other coordinate. -/
theorem isFibrewiseRegularPair_of_first_eq_one
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (q : A) :
    IsFibrewiseRegularPair φ 1 q := by
  constructor
  · intro I
    exact (isUnit_one : IsUnit (Ideal.Quotient.mk (I.map φ) (1 : A))).mem_nonZeroDivisors
  · intro I
    let S : Type v := A ⧸ Ideal.span ({1} : Set A)
    let J : Ideal S := I.map ((Ideal.Quotient.mk (Ideal.span ({1} : Set A))).comp φ)
    letI : Subsingleton S :=
      Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
    letI : Subsingleton (S ⧸ J) := ⟨fun _ _ => Subsingleton.elim _ _⟩
    change (Ideal.Quotient.mk J (Ideal.Quotient.mk (Ideal.span ({1} : Set A)) q)) ∈
      (S ⧸ J)⁰
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x _ ↦ Subsingleton.elim _ _, fun x _ ↦ Subsingleton.elim _ _⟩

/-- An affine change of the second normalized coordinate by a unit scale and
a multiple of the first member preserves fibrewise regularity. -/
theorem IsFibrewiseRegularPair.second_affine
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (p q r : A) (u : Aˣ)
    (hregular : IsFibrewiseRegularPair φ p q) :
    IsFibrewiseRegularPair φ p (q * u + p * r) := by
  exact (hregular.second_mul_unit φ p q u).second_add_first_mul φ p (q * u) r

/-- The two-generator quotient criterion in the form attached directly to a
ring map.  This avoids choosing an ambient algebra structure when the map is
the global-coordinate map of an affine scheme morphism. -/
theorem quotient_flat_of_two_nonZeroDivisors_over_ringHom
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.Flat) (p q : A)
    (hp : ∀ I : Ideal R,
      Ideal.Quotient.mk (I.map φ) p ∈ (A ⧸ I.map φ)⁰)
    (hq : ∀ I : Ideal R,
      Ideal.Quotient.mk
          (I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))
          (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
        ((A ⧸ Ideal.span {p}) ⧸
          I.map ((Ideal.Quotient.mk (Ideal.span {p})).comp φ))⁰) :
    ((Ideal.Quotient.mk (Ideal.span {p} ⊔ Ideal.span {q})).comp φ).Flat := by
  let _ : Algebra R A := φ.toAlgebra
  let _ : Module.Flat R A := hφ
  have h : Module.Flat R (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) :=
    quotient_flat_of_two_nonZeroDivisors_mod_base_ideals p q hp hq
  rw [← RingHom.flat_algebraMap_iff] at h
  exact h

/-- A fibrewise regular pair has flat two-generator quotient. -/
theorem quotient_flat_of_isFibrewiseRegularPair
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.Flat) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q) :
    ((Ideal.Quotient.mk (Ideal.span {p} ⊔ Ideal.span {q})).comp φ).Flat :=
  quotient_flat_of_two_nonZeroDivisors_over_ringHom φ hφ p q hregular.1 hregular.2

end AllCharacteristics
