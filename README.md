# Craig Interpolation for Skew Non-commutative Intuitionistic Linear Logic

The code includes:
- a cut-free sequent calculus ([SeqCalc.agda](https://github.com/niccoloveltri/code-skewmonclosed/tree/interpolation/SeqCalc.agda))
- a focused subsystem of sequent calculus derivations ([Focusing.agda](https://github.com/niccoloveltri/code-skewmonclosed/tree/interpolation/Focusing.agda))
- proof of Maehara-style interpolation: the interpolation procedure ([Interpolation.agda](https://github.com/niccoloveltri/code-skewmonclosed/tree/interpolation/Interpolation.agda)), the variable condition ([VarCondition.agda](https://github.com/niccoloveltri/code-skewmonclosed/tree/interpolation/VarCondition.agda)), the proof that interpolation is right inverse to cut ([CutInterpolation.agda](https://github.com/niccoloveltri/code-skewmonclosed/tree/interpolation/CutInterpolation.agda))

The main file containing the whole development is [Main.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/Main.agda).

The formalization uses Agda 2.6.2. 
