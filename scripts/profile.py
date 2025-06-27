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
    "Palamedes/Examples/Tree/BST/BST.lean",
]

# Regular expression to match the desired output
pattern = re.compile(r'\[palamedes\.trace\] \[(\d+(?:\.\d+)?)\] ⟪(.+)⟫')

# Dictionary to store extracted numbers by string
data = defaultdict(list)

# Run the external script multiple times
for file in tqdm(FILES * NUM_RUNS):
    try:
        result = subprocess.run(BASE_CMD + [file],
                                capture_output=True,
                                text=True,
                                check=True)
        output = result.stdout
        matches = pattern.findall(output)
        for (numRepr, label) in matches:
            data[label].append(float(numRepr))
    except subprocess.CalledProcessError as e:
        print(f"Error running script: {e}")

label_pattern = re.compile(r"fun (.+) => (.+)")

# Compute and print mean and standard deviation
for label, numbers in data.items():
    mean = statistics.mean(numbers)
    stdev = statistics.stdev(numbers)

    label = label.replace("∃", "`$\\exists$`")
    label = label.replace("∨", "`$\\lor$`")
    label = label.replace("∧", "`$\\land$`")
    label = label.replace("≤", "<=")
    label = label.replace("TARGET", "`\\textbf{v}`")

    print(
        "\\mintinline[mathescape=true,escapeinside=``]{text}" +
        f"|{label}| & $\checkmark$ & ${mean * 1000:.2f}$ & (${stdev * 1000:.2f}$) \\\\"
    )
