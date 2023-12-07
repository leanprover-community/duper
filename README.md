# Duper

Duper is an automatic proof-producing theorem prover broadly similar to Isabelle's `Metis`. Duper has primarily been developed by Joshua Clune (Github: JOSHCLUNE), Yicheng Qian (Github: PratherConid), and Alex Bentkamp (Github: abentkamp). It is currently in active development and pull requests are welcome. For additional questions or bug reports, feel free to reach out to Joshua Clune on [Lean Zulip](https://leanprover.zulipchat.com).

## Building/Installation

With [elan](https://github.com/leanprover/elan) installed, cloning this repository and running `lake build` in the root directory should suffice to build and test Duper. Duper itself does not depend on Mathlib, so we additionally include a subdirectory DuperOnMathlib which has its own lakefile that imports both Duper and Mathlib. To build this subdirectory, we recommend navigating to DuperOnMathlib and running `lake exe cache get` followed by `lake build`.

## Adding Duper to Your Project

To use Duper in a Lean 4 project, first add this package as a dependency. In your lakefile.lean, add:

```lean
require duper from git "https://github.com/leanprover-community/duper.git"
```

Then, make sure that your `lean-toolchain` file contains the same version of Lean 4 as Duper and that if your project imports [std4](https://github.com/leanprover/std4.git), then it uses the same version of std4 as [Auto](https://github.com/leanprover-community/lean-auto.git). This step is necessary because Duper depends on Auto which depends on std4, so errors can arise if your project attempts to import a version of std4 different from the one imported by Duper.

After these steps are taken, the following testfile should successfully compile:
```lean
import Duper.Tactic

example : True := by duper
```

## Using Duper

Duper is a terminal tactic that will look at the current main goal and either solve it or throw an error. The syntax for invoking Duper in tactic mode is `duper [facts] {options}`. The `facts` argument is used to indicate which lemmas or propositions Duper should attempt to use to prove the goal, and the `options` argument is used to specify how Duper should be called.

### Facts

The `facts` supplied to Duper are separated by commas and can include:
- Hypotheses (of type `Prop`) from the local context
- External lemmas
- The symbol `*` to indicate that Duper should consider all proofs in the current local context

If the `[facts]` argument are omitted from the Duper call, then Duper will only reason about the goal, meaning `by duper` is equivalent to `by duper []`. Duper performs best when it is given a minimal set of facts that can be used to prove the goal, and it also performs better when more specific lemmas are used (e.g. Duper will generally perform better if given `Nat.mul_one` rather than `mul_one`, though it is capable of working with either). We do not yet have Duper connected to a relevance filter so for now it is necessary to manually provide Duper all of the lemmas it needs, though we hope to improve this state of affairs in the future.

### Options

Each of the `options` supplied to Duper have the form `option := value` and are separated by commas. Options that can be used to customize a Duper call include:
- `portfolioInstance`: Can be set to a natural number from 0 to 24. Each of these numbers corresponds to an exact set of options by which Duper can be called, so specifying the portfolioInstance option makes specifying any additional options redundant. The primary use for the portfolioInstance option is to ensure that when `duper?` succeeds, a short proof script of the form `by duper [facts] {portfolioInstance := n}` can be recommended to the user.
- `portfolioMode`: Can be set to `true` or `false` and is set to `true` by default. If portfolioMode is enabled, then Duper will call 3-4 instances of itself with different option configurations, and if portfolioMode is disabled, then Duper will only call a single instance of itself. The benefit of enabling portfolioMode is that different option configurations are better suited to different problems, while the downside is that if portfolioMode is enabled, each instance of Duper is given less time to run before timing out. Generally, we recommend users keep portfolioMode enabled by default and use `set_option maxHeartbeats` to control how long they would like each Duper instance to run before giving up (if `maxHeartbeats` is set to `n`, each instance will be allocated approximately `n/3` heartbeats).
- `preprocessing`: Can be set to `full`, `monomorphization`, or `no_preprocessing`. This option will control the extent to which lemmas are preprocessed before being given to Duper. When portfolioMode is enabled and the preprocessing option is not specified, 3-4 instances will have full preprocessing and 1 instance will have no preprocessing. But when the preprocessing option is enabled, all attempted instances will use the specified preprocessing option. Generally, we recommend users do not specify the preprocessing option unless specifically prompted to by Duper.
- `inhabitationReasoning`: Can be set to `true` or `false`. If the goal or any provided lemmas include potentially empty types, Duper has to perform additional reasoning to guarantee the correctness of its proofs. If the user is confident that all types in the problem are provably nonempty, even outside the context of the current problem, then setting inhabitationReasoning to false can help Duper reason more efficiently (though during proof reconstruction, Duper will still verify that any assumptions made about type inhabitation are valid). Likewise, if the user is confident that there is at least one type in the problem that is either empty or can only be verified as nonempty using facts in the current context, then setting inhabitationReasoning to true will ensure that all Duper instances perform the necessary type inhabitation reasoning from the getgo.
- `includeExpensiveRules`: Can be set to `true` or `false`. Some of the rules that Duper uses to reason about higher-order problems can significantly worsen Duper's performance. Additionally, one of Duper's rules evaluates decidability instances, which can be prohibitively expensive for some problems. Setting includeExpensiveRules to false can make Duper's search more efficient by skipping these rules that have the potential to consume a significant portion of Duper's runtime.

### Proof Scripts

Although we recommend enabling Duper's portfolio mode to find initial proofs, running multiple instances of Duper is less efficient than just running the single instance that the user knows will find the proof. By calling `duper?` rather than `duper`, you can instruct Duper to generate a tactic script of the form `duper [facts] {portfolioInstance := n}` which will call just the Duper instance that was successful in proving the current goal.

### Debugging

The fact that Duper is a saturation-based theorem prover (meaning it attempts to prove the goal by negating the target and generating clauses until it derives a contradiction) creates some inherent debugging challenges. If Duper fails to prove a particular goal because it timed out, then it likely generated hundreds or thousands of clauses in the attempt. Often, the volume of generated clauses makes understanding why Duper failed to prove the goal prohibitively time-consuming. Nonetheless, for the minority of cases where it is feasible to understand why Duper failed, we provide a variety of trace options to facilitate examination of the Duper's state.

If Duper times out, the following trace options are available:
- Using `set_option trace.duper.timeout.debug true` will cause Duper to print:
    - The total number of clauses in the active set (these are the clauses that Duper has proven and fully processed)
    - The total number of clauses in the passive set (these are the clauses that Duper has proven but has not yet fully processed)
    - The total number of generated clauses
    - The set of unit clauses in the active set (i.e. the set of fully processed clauses that can be expressed as equalities or inequalities)
    - Information about types that have been identified in the problem and whether they are provably inhabited by typeclass reasoning, provably nonempty from assumptions given to duper, or potentially uninhabited
- Using `set_option trace.duper.timeout.debug.fullActiveSet true` will cause Duper to print the full active set (i.e. all clauses that Duper has fully processed, not just those that can be expressed with a single equality or inequality). Note that for some problems, enabling this option can cause VSCode to crash (because it struggles to handle the amount of trace output).
- Using `set_option trace.duper.timeout.debug.fullPassiveSet true` will cause Duper to print the full passive set (i.e. all clauses that Duper has proven but not yet fully processed). Note that for some problems, enabling this option can cause VSCode to crash (because it struggles to handle the amount of trace output).

If Duper saturates, meaning Duper fully processed all clauses and was unable to generate more, then `set_option trace.duper.saturate.debug true` will cause Duper to print:
- The final active set (i.e. all clauses that Duper generated and fully processed)
- Information about types that have been identified in the problem and whether they are provably inhabited by typeclass reasoning, provably nonempty from assumptions given to duper, or potentially uninhabited

If Duper successfully proves the goal and you want to obtain additional information about the proof Duper found, then `set_option trace.duper.printProof true` will show the clauses used in the final proof and `set_option trace.duper.proofReconstruction true` will show information about the proofs of said clauses and the final proof that was used to resolve the goal.

In our experience, we have generally found attempting to debug problems that Duper saturates on to be more fruitful than problems that Duper timed out on (because there is typically a smaller volume of clauses to look at). This is most helpful when Duper is capable of solving a problem in principle but needs to be provided some additional fact that it is not natively aware of. Additionally, we have generally found trace output to be more readable when preprocessing is disabled, since the current preprocessing procedure transforms input lemmas into facts with uninformative names. If you need to look at Duper's trace output even with preprocessing enabled, then `set_option trace.duper.monomorphization.debug true` will cause Duper to print its input facts before and after the monomorphization procedure. This can help in understanding how the monomorphized constants that appear in Duper's clauses correspond to constants in the original problem.