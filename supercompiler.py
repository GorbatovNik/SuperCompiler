from residual_program_generator import *
from advanced_process_tree_builder import *
import global_vars
import argparse
from front import parse_program
import os
from PyPDF2 import PdfMerger


def merge_pdfs(directory, output):
    # Сбор всех PDF файлов в указанной директории
    pdf_files = [os.path.join(directory, f) for f in os.listdir(directory) if f.endswith('.pdf')]
    
    # Сортировка файлов в алфавитном порядке
    pdf_files.sort()
    
    # Объединение PDF файлов
    merger = PdfMerger()
    for pdf in pdf_files:
        merger.append(pdf)
    merger.write(output)
    merger.close()
    os.startfile(output)

def read_scala_file(file_path):
    try:
        with open(file_path, 'r') as file:
            return file.read()
    except FileNotFoundError:
        print(f"Error: The file {file_path} was not found.")
        return None
    except Exception as e:
        print(f"An error occurred while reading the file: {e}")

def test(scala_code):
    global_vars.debug = False
    global_vars.stats = False
    global_vars.test = True
    sll_prog, sll_task = parse_program(scala_code)
    nameGen = NameGen("v", 100)
    tree = buildAdvancedProcessTree(nameGen, 100, sll_prog, sll_task)
    ARPG = advancedResidualProgramGenerator(tree)
    scala = ARPG.generate_scala()
    return scala


def main(file_path, debug):
    file_name = os.path.splitext(os.path.basename(file_path))[0]
    global_vars.debug = debug
    scala_code = read_scala_file(file_path)
    if scala_code is not None:
        print(f"Processing file: {file_path}")
        print(f"File content:\n{scala_code}\n")
        
        sll_prog, sll_task = parse_program(scala_code)
        nameGen = NameGen("v", 100)
        tree = buildAdvancedProcessTree(nameGen, 100, sll_prog, sll_task)
        ARPG = advancedResidualProgramGenerator(tree)
        scala = ARPG.generate_scala()
        print("\nResidual program:")
        print(scala)
        tree.render("last", release=True)
        merge_pdfs("progress/", file_name + ".pdf")
    else:
        print("Failed to read the file.")
    

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Process a .scala file.")
    parser.add_argument('scala_file', type=str, help='Path to the .scala file')
    parser.add_argument('--debug', action='store_true', help='Enable debug mode')
    
    args = parser.parse_args()
    
    global_vars.debug = args.debug
    main(args.scala_file, args.debug)
