import AllCharacteristics.SmoothCubicJacobianProjectiveEmpty
import AllCharacteristics.CubicPencil
import Mathlib.AlgebraicGeometry.FunctionField

/-! SOURCE ONLY / UNVERIFIED. Literal TeX1189–1194 method: the actual
projective derivative-image over A1 is closed, misses t=1, and misses the
generic point. No universal nonzero-smooth parameter open is used. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] PrimeSpectrum.isPrime
variable {k : Type u} [Field k]

def cubicPencilJacobianImage (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    Set (Spec (.of (Polynomial k))) :=
  Set.range (toBase (cubicJacobianIdeal (cubicPencil p g)
    (cubicPencil_isHomogeneous hp hg)))

theorem cubicPencilJacobianImage_isClosed
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    IsClosed (cubicPencilJacobianImage p g hp hg) :=
  cubicJacobianProjection_range_isClosed _ _

/-- The reference fiber is the SAME original g at t=1. Properness and the
empty Jacobian fiber are derived, not premises in this pencil factory. -/
theorem cubicPencilJacobianImage_not_mem_one
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : k)))
        (IsLocalRing.closedPoint k) ∉ cubicPencilJacobianImage p g hp hg := by
  let P := cubicPencil p g
  have hP : P.IsHomogeneous 3 := cubicPencil_isHomogeneous hp hg
  let I := cubicJacobianIdeal P hP
  let J := cubicJacobianIdeal g hg
  let e₁ : Polynomial k →+* k := Polynomial.evalRingHom 1
  have hmap : I.toIdeal.map (MvPolynomial.map e₁) = J.toIdeal := by
    have he := cubicJacobianIdeal_map e₁ P hP
    simpa only [P, e₁, cubicPencil_map_eval_one] using he
  let e := projectiveBaseChangeIso e₁ I J hmap
  letI : IsEmpty (scheme J) := smoothCubic_cubicJacobianScheme_isEmpty g hg hg0
  intro hone
  have hpre : IsLocalRing.closedPoint k ∈
      Set.range (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom e₁))) := by
    rw [Scheme.Pullback.range_snd]
    exact hone
  obtain ⟨z, hz⟩ := hpre
  exact isEmptyElim (e.inv z)

/-- Any injective field-valued parameter is generic in A1. Closedness of the
ACTUAL derivative-image plus its omission of t=1 excludes that parameter. -/
theorem cubicPencilJacobianImage_not_mem_injective_parameter
    {K : Type u} [Field K] (a : Polynomial k →+* K) (ha : Function.Injective a)
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    Spec.map (CommRingCat.ofHom a) (IsLocalRing.closedPoint K) ∉
      cubicPencilJacobianImage p g hp hg := by
  let η : PrimeSpectrum (Polynomial k) :=
    PrimeSpectrum.comap a (IsLocalRing.closedPoint K)
  let x₁ : PrimeSpectrum (Polynomial k) :=
    PrimeSpectrum.comap (Polynomial.evalRingHom 1) (IsLocalRing.closedPoint k)
  have hη : η.asIdeal = ⊥ := by
    rw [show η.asIdeal = RingHom.ker a from fieldPoint_asIdeal_eq_ker a]
    exact (RingHom.injective_iff_ker_eq_bot a).mp ha
  have hle : η ≤ x₁ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, hη]
    exact bot_le
  have hs : Specializes η x₁ := (PrimeSpectrum.le_iff_specializes η x₁).mp hle
  have hx : x₁ ∈ (cubicPencilJacobianImage p g hp hg)ᶜ :=
    cubicPencilJacobianImage_not_mem_one p g hp hg hg0
  exact hs.mem_open (cubicPencilJacobianImage_isClosed p g hp hg).isOpen_compl hx

/-- The coefficient-changed derivative scheme itself has no points at an
injective field-valued parameter. This retains the actual ideal/partials. -/
theorem cubicPencil_mappedJacobianScheme_isEmpty
    {K : Type u} [Field K] (a : Polynomial k →+* K) (ha : Function.Injective a)
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    IsEmpty (scheme (cubicJacobianIdeal ((cubicPencil p g).map a)
      ((cubicPencil_isHomogeneous hp hg).map a))) := by
  let P := cubicPencil p g
  have hP : P.IsHomogeneous 3 := cubicPencil_isHomogeneous hp hg
  let I := cubicJacobianIdeal P hP
  let J := cubicJacobianIdeal (P.map a) (hP.map a)
  have hmap : I.toIdeal.map (MvPolynomial.map a) = J.toIdeal :=
    cubicJacobianIdeal_map a P hP
  let e := projectiveBaseChangeIso a I J hmap
  refine ⟨fun z => ?_⟩
  have he : pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom a))
      (e.hom z) = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hpoint : Spec.map (CommRingCat.ofHom a) (IsLocalRing.closedPoint K) ∈
      cubicPencilJacobianImage p g hp hg := by
    have hr : IsLocalRing.closedPoint K ∈
        Set.range (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom a))) :=
      ⟨e.hom z, he⟩
    rw [Scheme.Pullback.range_snd] at hr
    exact hr
  exact cubicPencilJacobianImage_not_mem_injective_parameter a ha p g hp hg hg0 hpoint

end AllCharacteristics
