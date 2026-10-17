import PfaffianDescent.PolynomialPrincipalKaehlerFiberDimension
import PfaffianDescent.VoisinSmoothCubicEliminatedJacobian

/- SOURCE ONLY / UNVERIFIED. Dimension of the genuine chart Kähler
fiber at any actual field-valued chart point. Smoothness derives the
nonzero residue gradient internally; no rank/dimension certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry MvPolynomial TensorProduct KaehlerDifferential
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- This is the actual Kähler differential module of the cubic's actual
chart algebra, at the supplied original field-valued point. -/
theorem smoothCubic_actualKaehlerChartFiber_finrank_two
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* L) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra (ChartRing (equationIdeal p hp) j) L := g.toAlgebra
    Module.finrank L (L ⊗[ChartRing (equationIdeal p hp) j]
      KaehlerDifferential K (ChartRing (equationIdeal p hp) j)) = 2 := by
  classical
  let I := equationIdeal p hp
  let A := ChartRing I j
  let σ := {i : Fin 4 // i ≠ j}
  letI aK : Algebra K A := (chartBaseMap I j).toAlgebra
  letI : SMul K A := aK.toSMul
  letI : Algebra A L := g.toAlgebra
  let e : MvPolynomial σ K →ₐ[K] A := aeval (fun i => chartCoordinate I j i.val)
  letI aPoly : Algebra (MvPolynomial σ K) A := e.toRingHom.toAlgebra
  letI : SMul (MvPolynomial σ K) A := aPoly.toSMul
  letI : IsScalarTower K (MvPolynomial σ K) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (e.commutes c).symm)
  obtain ⟨he, hker, _⟩ := smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 j
  have hgrad : ∃ i : σ, g (e (pderiv i (coordinateOneEvaluation j p))) ≠ 0 := by
    by_contra hn
    push Not at hn
    have hle : Ideal.span (Set.range (fun i : σ =>
        e (pderiv i (coordinateOneEvaluation j p)))) ≤ RingHom.ker g := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hn i
    rw [smoothCubic_eliminatedChart_jacobian_top p hp hp0 j] at hle
    have h1 := hle (show (1 : A) ∈ ⊤ from trivial)
    have : (1 : L) = 0 := by simpa only [RingHom.mem_ker, map_one] using h1
    exact one_ne_zero this
  have hdim := polynomialPrincipal_kaehler_fiber_finrank_add_one
    (k := K) (A := A) (L := L) (σ := σ) he (coordinateOneEvaluation j p) hker hgrad
  have hcard : Fintype.card σ = 3 := by
    change Fintype.card {i : Fin 4 // ¬ i = j} = 3
    rw [Fintype.card_subtype_compl (fun i : Fin 4 => i = j)]
    simp
  rw [hcard] at hdim
  change Module.finrank L (L ⊗[A] KaehlerDifferential K A) = 2
  omega

end PfaffianDescent
