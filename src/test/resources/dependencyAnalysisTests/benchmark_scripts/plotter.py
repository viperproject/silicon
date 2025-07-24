import matplotlib.pyplot as plt
import numpy as np

def import_result(file: str):
  with open(file, mode="r") as f:
    contents = f.readlines()
  header = [c.strip() for c in contents[0].split(";")]
  results = {}
  for line in contents[1:]:
      parts = line.split(';')
      test_name = parts[0].strip()
      runtimes = [float(x.strip()) for x in parts[1:]]
      results[test_name] = runtimes
  return header, results

def plot_absolute_runtimes(header: list[str], test_results: dict[str, list[float]], out_file: str):
  names = []
  result1 = []
  result2 = []
  for name, result in test_results.items():
    names.append(name)
    result1.append(result[0])
    result2.append(result[1])

  x = np.arange(len(names))
  width = 0.35

  fig, ax = plt.subplots()
  ax.bar(x - width/2, result1, width, label=header[1])
  ax.bar(x + width/2, result2, width, label=header[2])

  ax.set_ylabel('Runtime (ms)')
  ax.set_title('Absolute Runtimes in ms')
  ax.set_xticks(x)
  ax.set_xticklabels(names, rotation=90)
  ax.legend()

  plt.tight_layout()
  plt.show()
  plt.savefig(out_file.replace(".out", "_absolute_runtimes.png"))

def plot_overhead(header: list[str], test_results: dict[str, list[float]], out_file: str):
  names = []
  result1 = []
  for name, result in test_results.items():
    names.append(name)
    result1.append(result[2])

  fig, ax = plt.subplots()
  ax.bar(names, result1, label=header[3])

  ax.set_ylabel('analysis runtime/baseline runtime')
  ax.set_title('Overhead of the Analysis')
  ax.set_xticklabels(names, rotation=90)
  ax.legend()

  plt.tight_layout()
  plt.show()
  plt.savefig(out_file.replace(".out", "_overhead.png"))

def plot_overhead_vs_program_size(header: list[str], test_results: dict[str, list[float]], out_file: str):
  names = []
  result1 = []
  result2 = []
  for name, result in test_results.items():
    names.append(name)
    result1.append(result[2])
    result2.append(result[3])

  plt.scatter(result2, result1)

  plt.ylabel('analysis runtime/baseline runtime')
  plt.xlabel('program size (#lines of code)')
  plt.title('Overhead of the Analysis vs Program Size')
  plt.legend()

  plt.grid(True)
  plt.tight_layout()
  plt.show()
  plt.savefig(out_file.replace(".out", "_overhead_vs_size.png"))

input_file = input("Input file: ")
header, result = import_result(input_file)

plot_absolute_runtimes(header, result, input_file)
plot_overhead(header, result, input_file)
plot_overhead_vs_program_size(header, result, input_file)