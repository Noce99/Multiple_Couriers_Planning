#!/bin/bash

# Usage:
#   ./smt-opt <SMT-LIB file> <obj.var name> <initial bound> <solver> <min/max>
# No (get-model) query should in the SMT-LIB input file.

TIMEOUT=300 # Timeout in seconds. TODO: Set timeout as a parameter.
in_file=$1
obj_var=$2
obj_val=$3

if
  [ "$4" = 'z3' ];
then
  solver_cmd="z3 -in "
elif
  [ "$4" = 'cvc4' ];
then
  solver_cmd="cvc4 --lang smt --produce-models --incremental "
elif
  [ "$4" = 'cvc5' ];
then
  solver_cmd="cvc5 --produce-models --incremental "
else
  echo "Unknown solver!"
  exit 1
fi
if [ "$5" = 'max' ]; then
  # Maximization problem.
  rel='>='
  next=1
else
  # Minimization problem.
  rel='<='
  next=-1
fi

# Creating input/output pipes.
in_pipe=pipe.in
out_pipe=pipe.out
rm $in_pipe $out_pipe pkill sleep 2>/dev/null
mkfifo $in_pipe
mkfifo $out_pipe

# Block input pipe for $TIMEOUT seconds.
sleep $TIMEOUT > $in_pipe &
# Send piped input data to solver, and the output of solver to output pipe.
$solver_cmd < $in_pipe > $out_pipe &
# Feed input pipe with the queries SMT-LIB specified in the input file.
cat $in_file > $in_pipe
# SOL = 0 iff solver hasn't find any solution yet.
SOL=0

while read line < $out_pipe
do
  if [ ! "$line" = 'sat' ]; then
    break;
  fi
  SOL=1
  echo -e "$obj_var = $obj_val\n----------"
  # Updating obj. value (linear search). TODO: Implement binary search.
  obj_val=`awk -v ov=$obj_val -v n=$next 'BEGIN {ov = int(ov) + n; print ov}'`
  if
    [ $obj_val -lt 0 ]
  then
    # Adjusting for unary minus.
    echo "(assert ($rel $obj_var (-"`echo $obj_val | tr '-' ' '`")))" > $in_pipe
  else
    echo "(assert ($rel $obj_var $obj_val))" > $in_pipe
  fi
  echo "(check-sat)" > $in_pipe
#  echo "%%% Solving with $obj_var $rel $obj_val"
done

if
  [[ $SOL -eq 0 ]]
then
  if [ "$line" = 'unsat' ]; then
    echo '=====UNSATISFIABLE====='
  else
    echo '=====UNKNOWN====='
  fi
elif [ "$line" = 'unsat' ]; then
  echo '=========='
fi

rm $in_pipe $out_pipe pkill sleep 2>/dev/null
