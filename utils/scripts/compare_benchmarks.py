import argparse
import pandas as pd # pip install pandas
import pandas_schema as pds # pip install pandas_schema
import dataclasses # Python 3.7?
import logging
import importlib # Python >= 3.5


# An attempt at modelling a Scala-like singleton object literal
@dataclasses.dataclass
class ExpectedInputColumnHeaders:
  file: str = 'File'
  outputs: str = 'Outputs'
  mean: str = 'Mean [ms]'
  stddev: str = 'StdDev [ms]'
  relstddev: str = 'RelStdDev [%]'
  best: str = 'Best [ms]'
  median: str = 'Median [ms]'
  worst: str = 'Worst [ms]'

  def __post_init__(self):
    self.all = dataclasses.astuple(self)

input_headers = ExpectedInputColumnHeaders()


def configure_cli_parser(parser):
  parser.add_argument(
    "baseline",
    type=argparse.FileType('r'),
    help="CSV file with baseline benchmark results")
    
  parser.add_argument(
    "variant",
    type=argparse.FileType('r'),
    nargs='+',
    help="CSV file(s) with further benchmark results")

def main():
  logging.basicConfig(level=logging.INFO, format="[%(levelname)s] %(message)s")

  excel_library = 'openpyxl' # Alternative: xlsxwriter
  write_excel = importlib.util.find_spec(excel_library) is not None
  if not write_excel:
    logging.info("Couldn't find package {}, thus won't write Excel files".format(excel_library))

  parser = argparse.ArgumentParser()
  configure_cli_parser(parser)
  args = parser.parse_args()

  files: List[io.TextIOWrapper] = \
    [args.baseline] + args.variant

  input_data: List[pd.DataFrame] = \
    [pd.read_csv(file) for file in files]

  schema = pds.Schema([
    pds.Column(input_headers.file),
    pds.Column(input_headers.outputs, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.mean, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.stddev, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.relstddev, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.best, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.median, [pds.validation.CanConvertValidation(int)]),
    pds.Column(input_headers.worst, [pds.validation.CanConvertValidation(int)])
  ])

  for idx in range(len(files)):
    file = files[idx]
    data = input_data[idx]

    # Passing expected column headers to validate() has the effect that additional
    # columns in the CSV file are ignored, instead of being reported as an error.
    # See https://github.com/TMiguelT/PandasSchema/issues/12.
    errors = schema.validate(data, columns=input_headers.all)
    
    message = "Validating structure of {}: {} error(s)".format(file.name, len(errors))

    if errors:
      logging.error(message)
      for error in errors:
        logging.error("  {}".format(error))
    else:
      logging.info(message)

  baseline: pd.DataFrame = input_data[0]

  for idx in range(1, len(input_data)):
    variant: pd.DataFrame = input_data[idx]

    comparison: pd.DataFrame = \
      variant[[input_headers.file, input_headers.outputs, input_headers.mean]]

    comparison = pd.merge(
      comparison, 
      baseline[[input_headers.file, input_headers.outputs, input_headers.mean]], 
      how='outer', 
      on=input_headers.file,
      suffixes=('_base', '_var'))

    comparison = comparison.set_index(input_headers.file)

    # print(comparison.head())

    comparison['Consistency'] = \
      comparison[input_headers.outputs + '_var'] == comparison[input_headers.outputs + '_base']

    comparison['ΔMean [ms]'] = \
      comparison[input_headers.mean + '_var'] - comparison[input_headers.mean + '_base']
      
    comparison['ΔMean [%]'] = \
      (comparison['ΔMean [ms]'] / comparison[input_headers.mean + '_base']) * 100

    comparison = comparison.drop(columns=[
      input_headers.outputs + '_var', 
      input_headers.outputs + '_base'])


    comparison = comparison.rename(columns={
      input_headers.mean + '_var': 'Mean (V) [ms]',
      input_headers.mean + '_base': 'Mean (B) [ms]'})

    comparison = \
      comparison[[
        'Consistency', 
        'Mean (B) [ms]', 'Mean (V) [ms]',
        'ΔMean [ms]', 'ΔMean [%]'
      ]]

    # See https://stackoverflow.com/questions/25788037 for why encoding is UTF-16
    csv_filename = '{}__vs-base.csv'.format(files[idx].name)
    logging.info('Writing comparison to CSV file {}'.format(csv_filename))
    comparison.to_csv(csv_filename, encoding='utf-16')
    
    if write_excel:
      excel_filename = '{}__vs-base.xlsx'.format(files[idx].name)
      logging.info('Writing comparison to Excel file {}'.format(excel_filename))

      with pd.ExcelWriter(excel_filename, engine=excel_library) as writer:
        baseline.set_index(input_headers.file).to_excel(writer, sheet_name='Baseline')
        variant.set_index(input_headers.file).to_excel(writer, sheet_name='Variant')
        comparison.to_excel(writer, sheet_name='Comparison')

if __name__ == "__main__":
  main()
