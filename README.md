# Focusing for Skew Monoidal Closed Categories

The code includes two equivalent deductive systems for skew monoidal closed categories:
- a cut-free sequent calculus ([SeqCalc.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/SeqCalc.agda))
- a focused subsystem of sequent calculus derivations ([Focusing.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/Focusing.agda))
- proof of Maehara-style interpolation: the interpolation procedure ([Interpolation.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/Interpolation.agda)), the variable condition ([VarCondition.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/VarCondition.agda)), the proof that interpolation is right inverse to cut ([CutInterpolation.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/CutInterpolation.agda))

The main file containing the whole development is [Main.agda](https://github.com/niccoloveltri/code-skewmonclosed/blob/master/Main.agda).

The formalization uses Agda 2.6.2. 
