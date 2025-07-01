import subprocess
import re
from collections import defaultdict
import statistics
from tqdm import tqdm

NUM_RUNS = 10
BASE_CMD = [
    "lake",
    "env",
    "lean",
    "-Dtrace.profiler=true",
]
FILES = [
    "Palamedes/Examples/Simple/Eq2.lean",
    "Palamedes/Examples/Simple/Eq2'.lean",
    "Palamedes/Examples/Simple/Eq2Or5.lean",
    "Palamedes/Examples/Simple/Eq2Or5'.lean",
    "Palamedes/Examples/Simple/ThreePlusOne.lean",

    "Palamedes/Examples/Range/Between5And10.lean",
    "Palamedes/Examples/Range/BetweenLoAndHi.lean",
    "Palamedes/Examples/Range/Gt5.lean",
    "Palamedes/Examples/Range/OneOrInRange.lean",

    "Palamedes/Examples/Arbitrary.lean",
    "Palamedes/Examples/OptimizationTests.lean",

    "Palamedes/Examples/List/AllTwos/AllTwos.lean",
    "Palamedes/Examples/List/AllTwosEvenLen/AllTwosEvenLen.lean",
    "Palamedes/Examples/List/EvenLen/EvenLen.lean",
    "Palamedes/Examples/List/IncreasingByOne/IncreasingByOne.lean",
    "Palamedes/Examples/List/LengthK/LengthK.lean",
    "Palamedes/Examples/List/LengthKAllTwos/LengthKAllTwos.lean",
    "Palamedes/Examples/List/SortedBetween/SortedBetween.lean",
    "Palamedes/Examples/List/True/True.lean",

    "Palamedes/Examples/List/AllTwos/Fold.lean",
    "Palamedes/Examples/List/AllTwosEvenLen/Fold.lean",
    "Palamedes/Examples/List/EvenLen/Fold.lean",
    "Palamedes/Examples/List/IncreasingByOne/Fold.lean",
    "Palamedes/Examples/List/LengthK/Fold.lean",
    "Palamedes/Examples/List/LengthKAllTwos/Fold.lean",
    "Palamedes/Examples/List/SortedBetween/Fold.lean",
    "Palamedes/Examples/List/True/Fold.lean",

    "Palamedes/Examples/Tree/AllTwos/AllTwos.lean"
    "Palamedes/Examples/Tree/AVL/AVL.lean",
    "Palamedes/Examples/Tree/BST/BST.lean",
    "Palamedes/Examples/Tree/CompleteTree/CompleteTree.lean",
    "Palamedes/Examples/Tree/IncreasingByOne/IncreasingByOne.lean",
    "Palamedes/Examples/Tree/NETree/NETree.lean",

    "Palamedes/Examples/Tree/AllTwos/Fold.lean",
    "Palamedes/Examples/Tree/AVL/Fold.lean",
    "Palamedes/Examples/Tree/BST/Fold.lean",
    "Palamedes/Examples/Tree/CompleteTree/Fold.lean",
    "Palamedes/Examples/Tree/NETree/Fold.lean",

    "Palamedes/Examples/Stack/GoodStack.lean",
    "Palamedes/Examples/Stack/Fold.lean",

    "Palamedes/Examples/STLC/WellTyped.lean",
    "Palamedes/Examples/STLC/Fold.lean",
]

# Regular expression to match the desired output
pattern = re.compile(r'\[palamedes\.trace\] \[(\d+(?:\.\d+)?)\] ⟪(.+)⟫')

# Dictionary to store extracted numbers by string
data = dict()

# Run the external script multiple times
iter = tqdm(FILES * NUM_RUNS, dynamic_ncols=True)
for file in iter:
    iter.set_description(file)
    try:
        result = subprocess.run(BASE_CMD + [file],
                                capture_output=True,
                                text=True,
                                check=True)
        output = result.stdout
        matches = pattern.findall(output)
        for (numRepr, label) in matches:
            if label in data:
                data[label]["times"].append(float(numRepr))
            else:
                total = True
                with open(file, "r") as f:
                    if any(
                            map(lambda line: line.find("allow_partial") != -1,
                                f.readlines())):
                        total = False
                data[label] = {"times": [float(numRepr)], "total": total}
    except subprocess.CalledProcessError as e:
        print(f"Error running script: {e}")

label_pattern = re.compile(r"fun (.+) => (.+)")

# Compute and print mean and standard deviation
for label, numbers in data.items():
    mean = statistics.mean(numbers["times"])
    stdev = statistics.stdev(numbers["times"])
    total = numbers["total"]

    label = label.replace("∃", "`$\\exists$`")
    label = label.replace("∨", "`$\\lor$`")
    label = label.replace("∧", "`$\\land$`")
    label = label.replace("Γ", "`$\\Gamma$`")
    label = label.replace("τ", "`$\\tau$`")
    label = label.replace("≤", "<=")

    label = label.replace("TARGET", "`\\textbf{v}`")

    total_label = "\\checkmark" if total else "\\times"
    print(
        "\\mintinline[mathescape=true,escapeinside=``]{text}" +
        f"|{label}| & ${total_label}$ & ${int(mean * 1000)}$ & (${stdev * 1000:.1f}$) \\\\"
    )
