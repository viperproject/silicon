import os

def read_results_file(result_file_path: str) -> dict[tuple[str, str], list[tuple[str, float]]]:
  with open(result_file_path) as f:
    lines = f.readlines()

  current_test = None
  current_results = []
  results = {}

  for line in lines:
      line = line.strip()
      print(line)
      if not line or line.startswith("!") or line.startswith("Failed") \
        or "Skip" in line \
        or "does not verify" in line:
          continue
      if line.startswith("dependencyAnalysisTests/precisionTests/"):
          # Save previous block if any
          if current_test and current_results:
              results[current_test] = current_results
          # Start new block
          parts = line.strip().split(" - ")
          current_test = (parts[0], parts[1])
          current_results = []
      else:
          method_name, precision = map(str.strip, line.split(":"))
          current_results.append((method_name, float(precision)))

  if current_test and current_results:
      results[current_test] = current_results

  return results

def build_table(out_file_path: str, results: dict[tuple[str, str], list[tuple[str, float]]]):
    f = open(out_file_path, mode="w")
    header = sorted(set([interference_name for (_, interference_name) in results.keys()]))
    header_summary_columns = [] # /["|", "max", "min", "avg"]
    base_test_names = sorted(set([base_name.strip() for (base_name, _) in results.keys()]))
    column_1_width = max([len(h) for h in base_test_names]) + 4
    column_widths = [len(h + "  ") for h in (header + header_summary_columns)]
    f.write("".ljust(column_1_width) + " &  " + "  &  ".join(header + header_summary_columns))
    f.write("\n")

    for base_test in base_test_names:
        f.write(base_test.ljust(column_1_width))
        current_test_results = []
        for idx, h in enumerate(header):
            f.write(" & ")
            if not (base_test, h) in results.keys():
                f.write("NaN".center(column_widths[idx]))
                continue
            result = results[(base_test, h)]
            avg = sum([prec for (_, prec) in result]) / len(result)
            current_test_results.append(avg)
            f.write(f"{avg:.3f}".center(column_widths[idx]))

        # print summary
        # f.write("|".center(column_widths[idx+1]))
        # f.write(f"{max(current_test_results):.3f}".center(column_widths[idx+2]))
        # f.write(f"{min(current_test_results):.3f}".center(column_widths[idx+3]))
        # f.write(f"{sum(current_test_results)/len(current_test_results):.3f}".center(column_widths[idx+4]))
        f.write("\\\\ \n")

def build_table_transposed(out_file_path: str, results: dict[tuple[str, str], list[tuple[str, float]]]):
    f = open(out_file_path, mode="w")
    interference_names = sorted(set([interference_name for (_, interference_name) in results.keys()]))
    base_test_names = sorted(set([base_name.strip() for (base_name, _) in results.keys()]))
    base_test_names_striped = [n.replace("dependencyAnalysisTests/precisionTests/", "") for n in base_test_names]
    column_1_width = max([len(h) for h in interference_names]) + 4
    column_widths = [len(h + "  ") for h in (base_test_names_striped)]
    f.write("".ljust(column_1_width) + " &  " + "  &  ".join(["\\rotatebox{90}{" + b + "}" for b in base_test_names_striped]))
    f.write("\\\\ \\hline\n")

    for interference in interference_names:
        f.write(interference.replace("_", "\\_").ljust(column_1_width))
        current_test_results = []
        for idx, base_test in enumerate(base_test_names):
            f.write(" & ")
            if not (base_test, interference) in results.keys():
                f.write("NaN".center(column_widths[idx]))
                continue
            result = results[(base_test, interference)]
            avg = sum([prec for (_, prec) in result]) / len(result)
            current_test_results.append(avg)
            if avg == 1.0:
                f.write(f"{avg:.2f}".center(column_widths[idx]))
            else:
                f.write("\\cellcolor{red!30} " + f"{avg:.2f}".center(column_widths[idx]))
        f.write("\\\\ \n")

result_file_name = input("file name: ")
raw_results = read_results_file("silicon\\src\\test\\resources\\dependencyAnalysisTests\\precisionTests\\results\\" + result_file_name)

build_table("silicon\\src\\test\\resources\\dependencyAnalysisTests\\precisionTests\\results\\result_table.out", raw_results)
build_table_transposed("silicon\\src\\test\\resources\\dependencyAnalysisTests\\precisionTests\\results\\result_table_transposed.out", raw_results)