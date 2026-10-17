import PfaffianDescent.SectionRepresenterCech
import PfaffianDescent.VoisinTwistCechAggregate
import PfaffianDescent.VoisinStandardOpenExtVanishing

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

private abbrev P3Index := ULift.{u} (Fin 4)

private noncomputable def p3StandardOpenTop :
    P3Index → TopologicalSpace.Opens ↥(Proj PS).toPresheafedSpace :=
  fun i => p3StandardOpen (K := K) i.down

lemma p3StandardOpenTop_iSup :
    ⨆ i : P3Index, p3StandardOpenTop K i = ⊤ := by
  simpa [p3StandardOpenTop, iSup_ulift] using p3StandardOpen_iSup K

private def p3IndexFunEquiv (n : ℕ) :
    (Fin (n + 1) → P3Index) ≃ (Fin (n + 1) → Fin 4) where
  toFun f i := (f i).down
  invFun f i := ⟨f i⟩
  left_inv f := by
    funext i
    cases h : f i
    simp [h]
  right_inv f := by funext i; rfl

noncomputable abbrev p3SectionRepresenterCechChain :
    ChainComplex (Proj PS).Modules ℕ :=
  sectionRepresenterCechChain (Proj PS).ringCatSheaf
    (p3StandardOpenTop K)

noncomputable def p3NegativeTwistCechTermEquivPi (m n : ℕ) :
    (p3NegativeTwistCechComplex (K := K) m).X n ≃
      (∀ f : Fin (n + 1) → Fin 4, p3CechTermFamily K m n f) :=
  ((addCommGrpIsoAddEquiv
      (eqToIso (p3NegativeTwistCechComplex_X (K := K) m n))).trans
    (addCommGrpProductAddEquivPi (p3CechTermFamily K m n))).toEquiv

lemma p3NegativeTwistCechTermEquivPi_add (m n : ℕ)
    (x y : (p3NegativeTwistCechComplex (K := K) m).X n) :
    p3NegativeTwistCechTermEquivPi K m n (x + y) =
      p3NegativeTwistCechTermEquivPi K m n x +
        p3NegativeTwistCechTermEquivPi K m n y := by
  unfold p3NegativeTwistCechTermEquivPi
  exact map_add (((addCommGrpIsoAddEquiv
    (eqToIso (p3NegativeTwistCechComplex_X (K := K) m n))).trans
      (addCommGrpProductAddEquivPi (p3CechTermFamily K m n)))) x y

noncomputable def p3SectionRepresenterCechHomEquiv (m n : ℕ) :
    ((p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS m) ≃
      (p3NegativeTwistCechComplex (K := K) m).X n :=
  ((sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
    (p3StandardOpenTop K)
    (sheafOfModules PS m) n).trans
      (Equiv.piCongrLeft (fun f : Fin (n + 1) → Fin 4 =>
        p3CechTermFamily K m n f) (p3IndexFunEquiv n))).trans
      (p3NegativeTwistCechTermEquivPi K m n).symm

end PfaffianDescent.ProjectiveNegativeTwist
