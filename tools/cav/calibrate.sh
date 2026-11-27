#!/bin/bash
# calibrate.sh <rustlyn results dir> <roslyn results dir> [rustlyn out dir] [roslyn out dir]
# Says for each failure of a run.sh run what the real Roslyn does with the test (roslyn.sh run over the
# same tests), as `<name> <reason> <verdict>` in <rustlyn results dir>/calibrated.txt and on stdout:
#   real                  Roslyn's program reproduces .expected, rustlyn's does not;
#   environment-same      Roslyn's does not either (written for another runtime, OS or culture), and
#                         rustlyn prints what Roslyn's program prints;
#   environment-differs   ... and rustlyn prints something else;
#   environment-nocompile Roslyn does not compile it (against these assemblies);
#   skipped               needs ilasm, which roslyn.sh does not have;   unknown  not run by roslyn.sh.
# The program outputs are in `out` beside the results (rustlyn) and in <roslyn results dir>/out.
R=$1; L=$2; ROUT=${3:-$(dirname $R)/out}; LOUT=${4:-$L/out}
norm() { tr -s '[:space:]' ' ' | sed 's/^ //; s/ $//'; }
: > $R/calibrated.txt
while read -r name reason; do
  if [ "$reason" == ilasm ]; then v=skipped
  elif grep -qx -- "$name" $L/pass.txt; then v=real
  else
    lr=$(awk -v n="$name" '$1 == n { print $2 }' $L/fail.txt)
    case $lr in
      "") v=unknown ;;
      ilasm) v=skipped ;;
      compile) v=environment-nocompile ;;
      *) if [ "$(norm < $ROUT/$name/actual.txt 2> /dev/null)" == "$(norm < $LOUT/$name/actual.txt 2> /dev/null)" ]; then v=environment-same
         else v=environment-differs; fi ;;
    esac
  fi
  echo "$name $reason $v"
done < $R/fail.txt >> $R/calibrated.txt
cat $R/calibrated.txt
echo; echo "by verdict:"; awk '{print $3}' $R/calibrated.txt | sort | uniq -c | sort -rn
echo; echo "by class (failures, then each verdict):"
awk '{ split($1, p, "_"); c = p[1]; n[c]++; k[c " " $3]++; v[$3] = 1 }
  END { for (c in n) { s = n[c] " " c; for (x in v) if (k[c " " x]) s = s " " x "=" k[c " " x]; print s } }' $R/calibrated.txt | sort -rn
