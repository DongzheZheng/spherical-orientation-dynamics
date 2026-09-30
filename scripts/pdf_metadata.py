"""Write figure PDFs without author, document identifier or time metadata."""
from pathlib import Path


def clear_pdf_metadata(path: Path) -> None:
    from pypdf import PdfReader, PdfWriter
    from pypdf.generic import NameObject

    reader = PdfReader(path)
    writer = PdfWriter()
    writer.clone_document_from_reader(reader)
    writer.metadata = None
    writer.root_object.pop(NameObject("/Metadata"), None)
    writer._ID = None
    temporary = path.with_suffix(".clean.pdf")
    with temporary.open("wb") as stream:
        writer.write(stream)
    temporary.replace(path)
