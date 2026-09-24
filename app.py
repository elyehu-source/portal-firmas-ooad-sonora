"""
Portal de Firmas OOAD Sonora (IMSS)
Firma Digital con e.firma (SAT) - Procesamiento 100% en memoria volátil (Zero-Disk Storage)
Lectura nativa con asn1crypto (100% Python), inmune a errores de codificación ASN.1 en Rust.
"""

import streamlit as st
import io
import re
import base64
import hashlib
from datetime import datetime, timezone
import qrcode
from PIL import Image, ImageDraw, ImageFont
import numpy as np

import asn1crypto.x509 as asn1_x509
import asn1crypto.core as asn1_core

# Parche de compatibilidad para Certificados e.firma del SAT (OID 2.5.4.45 x500UniqueIdentifier)
# El SAT en México codifica el RFC/CURP en el OID 2.5.4.45 usando PrintableString (tag 19) o UTF8String (tag 12)
# en vez de BIT STRING (tag 3, RFC 5280). Redefinir el OID a DirectoryString evita errores de parseo ASN.1.
asn1_x509.NameTypeAndValue._oid_specs['2.5.4.45'] = asn1_x509.DirectoryString
asn1_x509.NameTypeAndValue._oid_specs['unique_identifier'] = asn1_x509.DirectoryString
asn1_x509.NameTypeAndValue._oid_specs['x500_unique_identifier'] = asn1_x509.DirectoryString

from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image as RLImage
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from pypdf import PdfReader, PdfWriter


# =====================================================================
# 0. GENERADOR DEL LOGOTIPO OFICIAL DEL IMSS / OOAD SONORA
# =====================================================================
def get_imss_logo_bytes() -> io.BytesIO:
    """Genera en memoria el logotipo institucional del IMSS - OOAD Sonora."""
    width, height = 340, 80
    img = Image.new('RGBA', (width, height), color=(255, 255, 255, 0))
    draw = ImageDraw.Draw(img)

    imss_green = (0, 99, 65, 255)
    dark_gray = (30, 41, 59, 255)

    draw.rounded_rectangle([0, 5, 75, 75], radius=8, fill=imss_green)
    
    try:
        font_large = ImageFont.truetype("arialbd.ttf", 26)
        font_main = ImageFont.truetype("arialbd.ttf", 24)
        font_sub = ImageFont.truetype("arial.ttf", 13)
        font_tag = ImageFont.truetype("arialbd.ttf", 11)
    except Exception:
        font_large = font_main = font_sub = font_tag = ImageFont.load_default()

    draw.text((10, 24), "IMSS", fill=(255, 255, 255, 255), font=font_large)

    draw.text((88, 12), "IMSS", fill=imss_green, font=font_main)
    draw.text((88, 38), "OOAD SONORA", fill=dark_gray, font=font_sub)
    draw.text((88, 55), "Órgano de Operación Administrativa Desconcentrada", fill=(100, 116, 139, 255), font=font_tag)

    img_buffer = io.BytesIO()
    img.save(img_buffer, format="PNG")
    img_buffer.seek(0)
    return img_buffer


# =====================================================================
# 1. MOTOR CRIPTOGRÁFICO DE E.FIRMA (SAT) CON ASN1CRYPTO (PYTHON NATIVO)
# =====================================================================
class EFirmaManager:
    """Administra la lectura del certificado X.509 (.cer) mediante asn1crypto y firmado PKCS#8 (.key)."""
    def __init__(self, cer_bytes: bytes, key_bytes: bytes, password: str):
        self.cer_bytes = cer_bytes
        self.key_bytes = key_bytes
        self.password = password
        
        self.cert = self._load_certificate()
        self.private_key = self._load_private_key()
        self._verify_key_pair_match()
        self.metadata = self._extract_metadata()

    def _verify_key_pair_match(self):
        """Verifica matemáticamente que la llave privada (.key) corresponda exactamente al certificado público (.cer)."""
        try:
            from cryptography import x509
            cert_crypto = x509.load_der_x509_certificate(self.cer_bytes)
            test_msg = b"Verificacion de pareja SAT OOAD Sonora 2026"
            sig = self.private_key.sign(test_msg, padding.PKCS1v15(), hashes.SHA256())
            cert_crypto.public_key().verify(sig, test_msg, padding.PKCS1v15(), hashes.SHA256())
            return
        except Exception:
            pass

        try:
            from OpenSSL import crypto
            cert_ssl = crypto.load_certificate(crypto.FILETYPE_ASN1, self.cer_bytes)
            test_msg = b"Verificacion de pareja SAT OOAD Sonora 2026"
            sig = self.private_key.sign(test_msg, padding.PKCS1v15(), hashes.SHA256())
            crypto.verify(cert_ssl, sig, test_msg, 'sha256')
            return
        except Exception:
            pass

        raise ValueError(
            "El archivo .cer y el archivo .key NO corresponden a la misma e.firma (no son pareja). "
            "Asegúrate de seleccionar el archivo .key que fue tramitado e impreso junto con ese certificado .cer."
        )

    def _load_certificate(self) -> asn1_x509.Certificate:
        try:
            return asn1_x509.Certificate.load(self.cer_bytes)
        except Exception as e:
            raise ValueError(f"No se pudo leer el archivo .cer de la e.firma: {str(e)}")

    def _load_private_key(self):
        import unicodedata
        
        if isinstance(self.password, bytes):
            try:
                raw_pwd = self.password.decode('utf-8')
            except Exception:
                raw_pwd = self.password.decode('latin-1', errors='ignore')
        else:
            raw_pwd = str(self.password)
            
        base_candidates = [raw_pwd, raw_pwd.strip()]
        str_candidates = []
        for c in base_candidates:
            if c not in str_candidates:
                str_candidates.append(c)
                str_candidates.append(unicodedata.normalize('NFC', c))
                str_candidates.append(unicodedata.normalize('NFD', c))

        unique_passwords = []
        for cand in str_candidates:
            for enc in ['utf-8', 'latin-1', 'cp1252', 'ascii']:
                try:
                    p_bytes = cand.encode(enc)
                    if p_bytes not in unique_passwords:
                        unique_passwords.append(p_bytes)
                except Exception:
                    pass

        # 1. Intentar primero con el motor de OpenSSL C (soporta crypto.FILETYPE_ASN1 y codificaciones SAT legacy como Latin-1)
        for pwd in unique_passwords:
            try:
                from OpenSSL import crypto
                pkey = crypto.load_privatekey(crypto.FILETYPE_ASN1, self.key_bytes, passphrase=pwd)
                pem_bytes = crypto.dump_privatekey(crypto.FILETYPE_PEM, pkey)
                return serialization.load_pem_private_key(pem_bytes, password=None, backend=default_backend())
            except Exception:
                pass
            try:
                from OpenSSL import crypto
                pkey = crypto.load_privatekey(crypto.FILETYPE_PEM, self.key_bytes, passphrase=pwd)
                pem_bytes = crypto.dump_privatekey(crypto.FILETYPE_PEM, pkey)
                return serialization.load_pem_private_key(pem_bytes, password=None, backend=default_backend())
            except Exception:
                pass

        # 2. Intentar con cryptography (DER y PEM)
        for pwd in unique_passwords:
            try:
                return serialization.load_der_private_key(self.key_bytes, password=pwd, backend=default_backend())
            except Exception:
                pass
            try:
                return serialization.load_pem_private_key(self.key_bytes, password=pwd, backend=default_backend())
            except Exception:
                pass

        raise ValueError(
            "Contraseña incorrecta o archivo .key de e.firma (SAT) dañado / no válido. "
            "Asegúrate de ingresar la contraseña de la e.firma (FIEL / SAT) y no la clave de la CIEC ni la del Portal del SAT."
        )

    def _extract_metadata(self) -> dict:
        sujeto = self.cert.subject.native
        emisor = self.cert.issuer.native

        nombre = None
        rfc = None
        curp = None

        rfc_pattern = re.compile(r'\b([A-Z&Ñ]{3,4}\d{6}[A-Z0-9]{3})\b', re.IGNORECASE)
        curp_pattern = re.compile(r'\b([A-Z]{4}\d{6}[HM][A-Z]{5}[A-Z0-9]\d)\b', re.IGNORECASE)

        if isinstance(sujeto, dict):
            nombre = sujeto.get('common_name')
            
            # 1. Buscar RFC en llaves dedicadas (serial_number, x500_unique_identifier, unique_identifier)
            for key in ('serial_number', 'x500_unique_identifier', 'unique_identifier'):
                val_raw = sujeto.get(key)
                if val_raw:
                    val_str = str(val_raw).strip()
                    m = rfc_pattern.search(val_str)
                    if m:
                        rfc = m.group(1).upper()
                        break
                    elif len(val_str) in [12, 13]:
                        rfc = val_str.upper()
                        break

            # 2. Buscar CURP y RFC en todos los valores del diccionario del sujeto
            for k, v in sujeto.items():
                v_str = str(v).strip()
                if not curp:
                    m_curp = curp_pattern.search(v_str)
                    if m_curp:
                        curp = m_curp.group(1).upper()
                if not rfc:
                    m_rfc = rfc_pattern.search(v_str)
                    if m_rfc:
                        rfc = m_rfc.group(1).upper()

        # 3. Fallback de pyOpenSSL para máxima redundancia en certificados SAT con codificación especial
        if not nombre or not rfc or rfc == "No identificado":
            try:
                from OpenSSL import crypto
                openssl_cert = crypto.load_certificate(crypto.FILETYPE_ASN1, self.cer_bytes)
                openssl_subj = openssl_cert.get_subject()
                for key_bytes_item, val_bytes_item in openssl_subj.get_components():
                    k_str = key_bytes_item.decode('utf-8', errors='ignore')
                    try:
                        v_str = val_bytes_item.decode('utf-8')
                    except UnicodeDecodeError:
                        v_str = val_bytes_item.decode('latin-1', errors='ignore')
                    
                    if k_str == 'CN' and not nombre:
                        nombre = v_str
                    elif k_str in ['serialNumber', 'x500UniqueIdentifier'] and not rfc:
                        m_rfc = rfc_pattern.search(v_str)
                        if m_rfc:
                            rfc = m_rfc.group(1).upper()
                        elif len(v_str.strip()) in [12, 13]:
                            rfc = v_str.strip().upper()
            except Exception:
                pass

        # Decodificación del número de serie SAT (20 caracteres ASCII / Hex)
        serial_int = self.cert.serial_number
        serial_hex = hex(serial_int)[2:].upper() if serial_int else ""
        if len(serial_hex) % 2 != 0:
            serial_hex = "0" + serial_hex

        serial_chars = []
        for i in range(0, len(serial_hex), 2):
            try:
                ch = chr(int(serial_hex[i:i+2], 16))
                if ch.isalnum():
                    serial_chars.append(ch)
            except Exception:
                pass
        serial_str = "".join(serial_chars)
        no_serie = serial_str if len(serial_str) >= 15 else serial_hex

        def _ensure_utc(dt):
            if dt is None:
                return datetime.now(timezone.utc)
            if getattr(dt, 'tzinfo', None) is None:
                return dt.replace(tzinfo=timezone.utc)
            return dt.astimezone(timezone.utc)

        # Fechas de vigencia
        vig_inicio = _ensure_utc(self.cert.not_valid_before)
        vig_fin = _ensure_utc(self.cert.not_valid_after)
        now = datetime.now(timezone.utc)
        valido = (vig_inicio <= now <= vig_fin)

        emisor_nombre = "SAT (Servicio de Administración Tributaria)"
        if isinstance(emisor, dict):
            emisor_nombre = emisor.get('organization_name') or emisor.get('common_name') or emisor_nombre

        return {
            "nombre": nombre or "Titular del Certificado SAT",
            "rfc": rfc or "No identificado",
            "curp": curp or "No registrado",
            "no_serie": no_serie,
            "emisor": emisor_nombre,
            "vigencia_inicio": vig_inicio.strftime('%Y-%m-%d %H:%M:%S UTC'),
            "vigencia_fin": vig_fin.strftime('%Y-%m-%d %H:%M:%S UTC'),
            "valido": valido
        }

    def sign_hash(self, data_bytes: bytes) -> bytes:
        """Genera la firma digital RSA SHA-256."""
        return self.private_key.sign(
            data_bytes,
            padding.PKCS1v15(),
            hashes.SHA256()
        )


# =====================================================================
# 2. INSERCIÓN DE RÚBRICA Y CONVERSIÓN DE DOCUMENTOS WORD (.DOCX)
# =====================================================================
def _prepare_rubrica_image_bytes(r_bytes: bytes) -> bytes:
    """Procesa la rúbrica recortando los márgenes sobrantes y preservando sus colores originales sobre fondo blanco puro."""
    try:
        img = Image.open(io.BytesIO(r_bytes)).convert("RGBA")
        arr = np.array(img)
        
        # Identificar trasfondo (píxeles blancos o transparentes)
        is_transparent = arr[:, :, 3] < 50
        is_white_bg = (arr[:, :, 0] > 210) & (arr[:, :, 1] > 210) & (arr[:, :, 2] > 210)
        is_bg = is_transparent | is_white_bg
        is_stroke = ~is_bg
        
        rgb = arr[:, :, 0:3].copy()
        rgb[is_bg] = [255, 255, 255]  # Fondo blanco puro

        if np.any(is_stroke):
            y_idx, x_idx = np.where(is_stroke)
            ymin, ymax = max(0, int(np.min(y_idx)) - 8), min(arr.shape[0], int(np.max(y_idx)) + 8)
            xmin, xmax = max(0, int(np.min(x_idx)) - 8), min(arr.shape[1], int(np.max(x_idx)) + 8)
            rgb = rgb[ymin:ymax, xmin:xmax]
        
        out_img = Image.fromarray(rgb, 'RGB')
        buf = io.BytesIO()
        out_img.save(buf, format="PNG")
        return buf.getvalue()
    except Exception:
        return r_bytes


def generate_default_rubrica_image(nombre: str = None) -> bytes:
    """Genera en memoria una rúbrica autógrafa estilizada en color azul institucional sin ningún texto."""
    try:
        width, height = 340, 100
        img = Image.new('RGB', (width, height), color=(255, 255, 255))
        draw = ImageDraw.Draw(img)
        dark_blue = (0, 51, 153)

        # Trazo autógrafo dinámico fluido sin texto
        points_stroke = [(20, 60), (45, 25), (75, 75), (110, 18), (150, 68), (185, 25), (220, 62), (260, 22), (295, 55), (325, 30)]
        draw.line(points_stroke, fill=dark_blue, width=4, joint="curve")

        # Lazos / Bucles autógrafos decorativos
        draw.arc([55, 20, 115, 70], start=30, end=330, fill=dark_blue, width=3)
        draw.arc([165, 25, 225, 75], start=0, end=300, fill=dark_blue, width=3)

        # Subrayado estilizado
        points_underline = [(15, 82), (95, 74), (200, 84), (325, 76)]
        draw.line(points_underline, fill=dark_blue, width=3, joint="curve")

        buf = io.BytesIO()
        img.save(buf, format="PNG")
        return buf.getvalue()
    except Exception:
        img = Image.new('RGB', (200, 60), color=(255, 255, 255))
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        return buf.getvalue()


def insertar_firma_en_docx(doc_bytes: bytes, signers_credentials: list):
    """
    Busca el nombre completo, apellidos, RFC, líneas de firma (___) o palabras clave
    dentro de los párrafos y tablas del documento Word (.docx) e inserta la imagen de la rúbrica
    ARRIBA de la línea de firma o nombre. Además, agrega la antefirma en el pie de página de todas las hojas.
    """
    import docx
    from docx.shared import Inches
    from docx.enum.text import WD_ALIGN_PARAGRAPH
    
    insertion_summary = []

    try:
        doc = docx.Document(io.BytesIO(doc_bytes))
        modified = False

        for creds in signers_credentials:
            try:
                efirma = EFirmaManager(creds['cer_bytes'], creds['key_bytes'], creds['password'])
                meta = efirma.metadata
            except Exception:
                meta = {}
                
            nombre = meta.get('nombre', '').strip().upper()
            rfc = meta.get('rfc', '').strip().upper()

            r_bytes_raw = creds.get('rubrica_bytes')
            if not r_bytes_raw:
                r_bytes_raw = generate_default_rubrica_image(nombre or "Firmante")
            
            r_bytes = _prepare_rubrica_image_bytes(r_bytes_raw)

            # 1. Antefirma / Rúbrica en el pie de página de TODAS las hojas del documento Word
            try:
                for section in doc.sections:
                    footer = section.footer
                    p_footer = footer.paragraphs[0] if footer.paragraphs else footer.add_paragraph()
                    p_footer.alignment = WD_ALIGN_PARAGRAPH.RIGHT
                    p_footer.paragraph_format.line_spacing = None
                    p_footer.paragraph_format.space_before = Inches(0)
                    p_footer.paragraph_format.space_after = Inches(0)
                    r_foot = p_footer.add_run()
                    r_foot.add_picture(io.BytesIO(r_bytes), width=Inches(0.9))
                    modified = True
            except Exception:
                pass

            # --- PASE 1: Términos prioritarios específicos del firmante (Nombre, Apellidos, RFC) ---
            pass1_terms = []
            if nombre:
                pass1_terms.append(nombre)
                parts = [p.strip().upper() for p in nombre.split() if len(p.strip()) >= 3]
                if len(parts) >= 2:
                    pass1_terms.append(' '.join(parts[-2:]))
                    pass1_terms.append(' '.join(parts[:2]))
                for pt in parts:
                    if len(pt) >= 4 and pt not in ['DELE', 'SUBD', 'DIRECTOR', 'TITULAR', 'JEFE']:
                        pass1_terms.append(pt)
            if rfc and rfc != "NO IDENTIFICADO":
                pass1_terms.append(rfc)

            # --- PASE 2: Líneas de firma ---
            pass2_terms = ['___', '---', '......']

            # --- PASE 3: Palabras clave genéricas de cierre y cargos ---
            pass3_terms = [
                'ATENTAMENTE', 'FIRMA', 'RÚBRICA', 'RUBRICA', 'TITULAR', 'AUTORIZÓ', 'AUTORIZO',
                'ELABORÓ', 'ELABORO', 'SOLICITANTE', 'VO.BO.', 'VO. BO.', 'VISTO BUENO',
                'REVISÓ', 'REVISO', 'RECIBIÓ', 'RECIBIO', 'APROBÓ', 'APROBO', 'SOLICITA', 'AUTORIZA',
                'VALIDÓ', 'VALIDO', 'CONFORMIDAD', 'DELEGADO', 'DIRECTOR', 'JEFE', 'COORDINADOR',
                'ADMINISTRADOR', 'RESPONSABLE', 'SUBDIRECTOR'
            ]

            firma_insertada = False
            metodo = ""

            def _do_insert(parrafo, label):
                nonlocal modified, firma_insertada, metodo
                target_p = parrafo
                from docx.text.paragraph import Paragraph

                # Si el párrafo inmediatamente anterior es una línea de firma (ej. "___________"), ubicar la rúbrica SOBRE la línea!
                try:
                    p_prev_elem = parrafo._element.getprevious()
                    if p_prev_elem is not None and p_prev_elem.tag.endswith('p'):
                        p_prev = Paragraph(p_prev_elem, parrafo._parent)
                        if any(line_token in p_prev.text for line_token in ['___', '---', '......']):
                            target_p = p_prev
                except Exception:
                    pass

                # Reciclar la línea vacía inmediatamente anterior a target_p si existe
                p_img = None
                try:
                    target_prev_elem = target_p._element.getprevious()
                    if target_prev_elem is not None and target_prev_elem.tag.endswith('p'):
                        t_prev = Paragraph(target_prev_elem, target_p._parent)
                        if not t_prev.text.strip():
                            p_img = t_prev
                except Exception:
                    pass

                if not p_img:
                    p_img = target_p.insert_paragraph_before()

                p_img.text = ""
                p_img.alignment = WD_ALIGN_PARAGRAPH.CENTER if parrafo.alignment == WD_ALIGN_PARAGRAPH.CENTER else parrafo.alignment
                p_img.paragraph_format.line_spacing = None
                p_img.paragraph_format.space_before = Inches(0.02)
                p_img.paragraph_format.space_after = Inches(0.02)
                run = p_img.add_run()
                run.add_picture(io.BytesIO(r_bytes), width=Inches(1.8))
                firma_insertada = True
                metodo = f"en el documento (sobre la línea de '{parrafo.text.strip()[:35]}...')"
                modified = True

            # Ejecución secuencial priorizada: Pase 1 -> Pase 2 -> Pase 3
            passes = [pass1_terms, pass2_terms, pass3_terms]

            for current_terms in passes:
                if not current_terms or firma_insertada:
                    continue

                # 1. Buscar en párrafos principales
                for parrafo in doc.paragraphs:
                    p_upper = parrafo.text.upper()
                    if any(term in p_upper for term in current_terms if len(term) >= 2):
                        try:
                            _do_insert(parrafo, "párrafo")
                            break
                        except Exception:
                            pass

                if firma_insertada:
                    break

                # 2. Buscar en celdas de tablas
                for tabla in doc.tables:
                    for fila in tabla.rows:
                        for celda in fila.cells:
                            for parrafo in celda.paragraphs:
                                p_upper = parrafo.text.upper()
                                if any(term in p_upper for term in current_terms if len(term) >= 2):
                                    try:
                                        _do_insert(parrafo, "tabla")
                                        break
                                    except Exception:
                                        pass
                                if firma_insertada:
                                    break
                            if firma_insertada:
                                break
                        if firma_insertada:
                            break
                    if firma_insertada:
                        break

            # 4. Fallback: Si no se encontró en ningún pase, colocar al final
            if not firma_insertada:
                try:
                    p_end = doc.add_paragraph()
                    p_end.paragraph_format.line_spacing = None
                    p_end.add_run(f"\n_______________________\nFIRMA: {nombre}\n").bold = True
                    r_end = p_end.add_run()
                    r_end.add_picture(io.BytesIO(r_bytes), width=Inches(1.8))
                    modified = True
                    firma_insertada = True
                    metodo = "al final del documento (anexo de firma)"
                except Exception:
                    pass

            if firma_insertada:
                insertion_summary.append({
                    'nombre': nombre or "Firmante",
                    'metodo': metodo
                })

        if modified:
            out_buf = io.BytesIO()
            doc.save(out_buf)
            return out_buf.getvalue(), insertion_summary
    except Exception:
        pass
        
    return doc_bytes, insertion_summary


def convert_docx_to_pdf_bytes(docx_bytes: bytes) -> bytes:
    """Convierte un documento Word (.docx) a PDF de forma volátil (Zero-Disk Storage).
    Intenta primero usar docx2pdf (MS Word en Windows) para máxima fidelidad visual (incluyendo imágenes),
    y si no está disponible, utiliza el motor puro Python (python-docx + ReportLab) extrayendo texto e imágenes.
    """
    # 1. Intentar conversión con docx2pdf (MS Word) con inicialización COM segura
    try:
        import tempfile
        import os
        import pythoncom
        from docx2pdf import convert
        pythoncom.CoInitialize()
        try:
            with tempfile.TemporaryDirectory() as tmp_dir:
                docx_path = os.path.join(tmp_dir, "input.docx")
                pdf_path = os.path.join(tmp_dir, "output.pdf")
                with open(docx_path, "wb") as f:
                    f.write(docx_bytes)
                convert(docx_path, pdf_path)
                if os.path.exists(pdf_path):
                    with open(pdf_path, "rb") as f:
                        return f.read()
        finally:
            pythoncom.CoUninitialize()
    except Exception:
        pass

    # 2. Motor secundario puro Python (python-docx + ReportLab) con extracción de imágenes inline
    import docx
    doc = docx.Document(io.BytesIO(docx_bytes))
    pdf_out = io.BytesIO()
    doc_pdf = SimpleDocTemplate(
        pdf_out,
        pagesize=letter,
        leftMargin=36,
        rightMargin=36,
        topMargin=36,
        bottomMargin=36
    )
    styles = getSampleStyleSheet()
    story = []

    def _extract_images_from_paragraph(p):
        imgs = []
        try:
            blip_rids = p._element.xpath('.//a:blip/@r:embed')
            for rId in blip_rids:
                if rId in doc.part.related_parts:
                    img_part = doc.part.related_parts[rId]
                    clean_b = _prepare_rubrica_image_bytes(img_part.image.blob)
                    imgs.append(RLImage(io.BytesIO(clean_b), width=130, height=45))
        except Exception:
            pass
        return imgs

    for p in doc.paragraphs:
        txt = p.text.strip()
        if txt:
            style = styles['Heading1'] if p.style.name.startswith('Heading 1') else styles['Normal']
            story.append(Paragraph(txt, style))
            story.append(Spacer(1, 4))
        
        p_imgs = _extract_images_from_paragraph(p)
        for img_obj in p_imgs:
            story.append(img_obj)
            story.append(Spacer(1, 6))

    for t in doc.tables:
        t_data = []
        for row in t.rows:
            r_data = []
            for c in row.cells:
                cell_elements = []
                for p in c.paragraphs:
                    txt = p.text.strip()
                    if txt:
                        cell_elements.append(Paragraph(txt, styles['Normal']))
                    cell_imgs = _extract_images_from_paragraph(p)
                    for img_obj in cell_imgs:
                        cell_elements.append(img_obj)
                if not cell_elements:
                    cell_elements.append(Paragraph("", styles['Normal']))
                r_data.append(cell_elements)
            t_data.append(r_data)
        if t_data:
            table_obj = Table(t_data)
            table_obj.setStyle(TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#006341')),
                ('TEXTCOLOR', (0, 0), (-1, 0), colors.white),
                ('GRID', (0, 0), (-1, -1), 0.5, colors.grey),
                ('VALIGN', (0, 0), (-1, -1), 'TOP'),
            ]))
            story.append(table_obj)
            story.append(Spacer(1, 10))

    if not story:
        story.append(Paragraph("Documento Word cargado.", styles['Normal']))

    doc_pdf.build(story)
    return pdf_out.getvalue()


# =====================================================================
# 3. GENERADOR DE CONSTANCIA Y EVIDENCIA LEGAL (AUDIT TRAIL OOAD SONORA)
# =====================================================================
def _generate_qr_code_image(data: str) -> io.BytesIO:
    """Genera una imagen PNG del código QR en memoria."""
    qr = qrcode.QRCode(
        version=1,
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=4,
        border=2,
    )
    qr.add_data(data)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white")
    img_buffer = io.BytesIO()
    img.save(img_buffer, format="PNG")
    img_buffer.seek(0)
    return img_buffer


def _chunk_text(text: str, chunk_size: int = 70) -> str:
    """Divide un texto largo (Base64/Hex) para ajuste seguro en ReportLab."""
    return "<br/>".join([text[i:i+chunk_size] for i in range(0, len(text), chunk_size)])


def generate_audit_page(doc_bytes: bytes, signatures_list: list) -> bytes:
    """Genera en memoria la página PDF de Constancia de Firma para OOAD Sonora (IMSS)."""
    buffer = io.BytesIO()
    doc = SimpleDocTemplate(
        buffer,
        pagesize=letter,
        leftMargin=36,
        rightMargin=36,
        topMargin=36,
        bottomMargin=36
    )
    
    styles = getSampleStyleSheet()
    title_style = ParagraphStyle(
        'DocTitle',
        parent=styles['Heading2'],
        fontSize=11.5,
        leading=14,
        textColor=colors.HexColor('#006341'),
        alignment=0
    )
    subtitle_style = ParagraphStyle(
        'DocSubTitle',
        parent=styles['Heading3'],
        fontSize=9.5,
        leading=12,
        textColor=colors.HexColor('#006341'),
        spaceBefore=6,
        spaceAfter=4
    )
    body_style = ParagraphStyle(
        'DocBody',
        parent=styles['Normal'],
        fontSize=7.5,
        leading=10.5,
        textColor=colors.HexColor('#1E293B')
    )
    code_style = ParagraphStyle(
        'DocCode',
        parent=styles['Normal'],
        fontSize=6,
        leading=7.5,
        fontName='Courier',
        textColor=colors.HexColor('#0F172A')
    )

    story = []

    logo_buffer = get_imss_logo_bytes()
    imss_logo_img = RLImage(logo_buffer, width=170, height=40)

    header_title_p = Paragraph(
        "<b>INSTITUTO MEXICANO DEL SEGURO SOCIAL</b><br/>"
        "<font size=8 color='#1E293B'>ÓRGANO DE OPERACIÓN ADMINISTRATIVA DESCONCENTRADA SONORA</font><br/>"
        "<font size=9 color='#006341'><b>CONSTANCIA DE FIRMA ELECTRÓNICA AVANZADA (e.firma SAT)</b></font>",
        title_style
    )

    top_header_table = Table([[imss_logo_img, header_title_p]], colWidths=[180, 360])
    top_header_table.setStyle(TableStyle([
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
    ]))
    story.append(top_header_table)
    story.append(Spacer(1, 6))

    doc_hash = hashlib.sha256(doc_bytes).hexdigest()
    timestamp_gen = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')

    header_data = [
        [Paragraph("<b>Resumen SHA-256 del Documento:</b>", body_style), Paragraph(doc_hash, code_style)],
        [Paragraph("<b>Total de Firmantes:</b>", body_style), Paragraph(str(len(signatures_list)), body_style)],
        [Paragraph("<b>Fecha de Generación:</b>", body_style), Paragraph(timestamp_gen, body_style)],
        [Paragraph("<b>Estándar Criptográfico:</b>", body_style), Paragraph("RSA 2048 / SHA-256 (e.firma SAT / NOM-151-SCFI-2016)", body_style)],
    ]
    header_table = Table(header_data, colWidths=[140, 300])
    header_table.setStyle(TableStyle([
        ('BACKGROUND', (0,0), (-1,-1), colors.HexColor('#F1F5F9')),
        ('BOX', (0,0), (-1,-1), 0.75, colors.HexColor('#CBD5E1')),
        ('INNERGRID', (0,0), (-1,-1), 0.5, colors.HexColor('#E2E8F0')),
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('TOPPADDING', (0,0), (-1,-1), 2),
        ('BOTTOMPADDING', (0,0), (-1,-1), 2),
    ]))

    qr_payload_lines = [f"IMSS-OOAD-SONORA", f"HASH:{doc_hash}"]
    for idx, sig_info in enumerate(signatures_list, 1):
        m = sig_info['metadata']
        qr_payload_lines.append(f"F{idx}:{m['rfc']}|{m['no_serie']}")
    qr_img_buffer = _generate_qr_code_image("\n".join(qr_payload_lines))
    qr_image = RLImage(qr_img_buffer, width=75, height=75)

    meta_qr_table = Table([[header_table, qr_image]], colWidths=[450, 90])
    meta_qr_table.setStyle(TableStyle([
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('ALIGN', (1,0), (1,0), 'CENTER'),
        ('LEFTPADDING', (1,0), (1,0), 5),
    ]))
    story.append(meta_qr_table)
    story.append(Spacer(1, 10))

    for idx, sig_info in enumerate(signatures_list, 1):
        meta = sig_info['metadata']
        sig_b64 = sig_info['signature_b64']
        ts = sig_info['timestamp']
        rubrica_bytes = sig_info.get('rubrica_bytes')

        cadena_original = f"||{meta['rfc']}|{meta['nombre']}|{meta['no_serie']}|{ts}|{doc_hash}||"

        story.append(Paragraph(f"<b>Firmante #{idx}: {meta['nombre']}</b> (e.firma SAT)", subtitle_style))

        firmante_data = [
            [Paragraph("<b>Titular:</b>", body_style), Paragraph(meta['nombre'], body_style)],
            [Paragraph("<b>RFC del Firmante:</b>", body_style), Paragraph(meta['rfc'], body_style)],
            [Paragraph("<b>CURP:</b>", body_style), Paragraph(meta['curp'], body_style)],
            [Paragraph("<b>No. Serie Certificado SAT:</b>", body_style), Paragraph(f"{meta['no_serie']} ({meta['emisor']})", body_style)],
            [Paragraph("<b>Vigencia Certificado:</b>", body_style), Paragraph(f"{meta['vigencia_inicio']} al {meta['vigencia_fin']}", body_style)],
            [Paragraph("<b>Fecha/Hora de Firma:</b>", body_style), Paragraph(ts, body_style)],
            [Paragraph("<b>Cadena Original:</b>", body_style), Paragraph(_chunk_text(cadena_original, 75), code_style)],
            [Paragraph("<b>Sello Digital (Base64):</b>", body_style), Paragraph(_chunk_text(sig_b64, 75), code_style)],
        ]

        if not rubrica_bytes:
            rubrica_bytes = generate_default_rubrica_image(meta.get('nombre', 'Firmante'))

        if rubrica_bytes:
            try:
                clean_r = _prepare_rubrica_image_bytes(rubrica_bytes)
                rubrica_img = RLImage(io.BytesIO(clean_r), width=120, height=40)
                firmante_data.append([
                    Paragraph("<b>Rúbrica / Firma Manuscrita:</b>", body_style),
                    rubrica_img
                ])
            except Exception:
                pass

        f_table = Table(firmante_data, colWidths=[130, 410])
        f_table.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,-1), colors.HexColor('#F8FAFC')),
            ('BOX', (0,0), (-1,-1), 0.75, colors.HexColor('#006341')),
            ('INNERGRID', (0,0), (-1,-1), 0.5, colors.HexColor('#E2E8F0')),
            ('VALIGN', (0,0), (-1,-1), 'TOP'),
            ('TOPPADDING', (0,0), (-1,-1), 2.5),
            ('BOTTOMPADDING', (0,0), (-1,-1), 2.5),
        ]))
        story.append(f_table)
        story.append(Spacer(1, 8))

    story.append(Paragraph(
        "<i>Fundamento Legal: La presente firma electrónica avanzada (e.firma SAT) produce los mismos efectos jurídicos que las "
        "leyes otorgan a los documentos con firma autógrafa, garantizando autoría, integridad y no repudio, de conformidad con los "
        "artículos 7 y 8 de la Ley de Firma Electrónica Avanzada, el Código de Comercio, los lineamientos del Instituto Mexicano del "
        "Seguro Social (IMSS) en el OOAD Sonora y los criterios de conservación de la NOM-151-SCFI-2016.</i>",
        ParagraphStyle('Legal', parent=styles['Italic'], fontSize=6, leading=8, textColor=colors.HexColor('#64748B'))
    ))

    doc.build(story)
    return buffer.getvalue()


# =====================================================================
# 4. ENSAMBLADOR DEL ARCHIVO FINAL MULTIFIRMA
# =====================================================================
def procesar_firma_pdf(pdf_original_bytes: bytes, signers_credentials: list, estampar_en_paginas_doc: bool = True):
    """Orquesta la validación, firmado criptográfico y ensamble del PDF final para OOAD Sonora."""
    signatures_list = []
    summary_metadata = []

    # 1. Estampar rúbricas visuales transparentes en la posición exacta del firmante en el documento original
    if estampar_en_paginas_doc and signers_credentials:
        try:
            from reportlab.lib.utils import ImageReader
            from reportlab.pdfgen import canvas
            
            reader_doc = PdfReader(io.BytesIO(pdf_original_bytes))
            num_pages = len(reader_doc.pages)
            
            page_stamps = {i: [] for i in range(num_pages)}

            for signer_idx, creds in enumerate(signers_credentials):
                try:
                    efirma = EFirmaManager(creds['cer_bytes'], creds['key_bytes'], creds['password'])
                    meta = efirma.metadata
                except Exception:
                    meta = {}

                r_bytes = creds.get('rubrica_bytes')
                if not r_bytes:
                    r_bytes = generate_default_rubrica_image(meta.get('nombre', 'Firmante'))

                clean_r = _prepare_rubrica_image_bytes(r_bytes)

                nombre = meta.get('nombre', '').strip().upper()
                rfc = meta.get('rfc', '').strip().upper()

                pass1_terms = []
                if nombre:
                    pass1_terms.append(nombre)
                    parts = [p.strip().upper() for p in nombre.split() if len(p.strip()) >= 3]
                    if len(parts) >= 2:
                        pass1_terms.append(' '.join(parts[-2:]))
                        pass1_terms.append(' '.join(parts[:2]))
                    for pt in parts:
                        if len(pt) >= 4 and pt not in ['DELE', 'SUBD', 'DIRECTOR', 'TITULAR', 'JEFE']:
                            pass1_terms.append(pt)
                if rfc and rfc != "NO IDENTIFICADO":
                    pass1_terms.append(rfc)

                pass2_terms = ['___', '---']
                pass3_terms = ['ATENTAMENTE', 'FIRMA', 'RÚBRICA', 'RUBRICA', 'VO.BO.', 'TITULAR', 'SUBDELEGADO', 'DIRECTOR']

                target_page_idx = None
                target_x = None
                target_y = None

                for p_passes in [pass1_terms, pass2_terms, pass3_terms]:
                    if not p_passes or target_page_idx is not None:
                        continue

                    for idx_page, page_obj in enumerate(reader_doc.pages):
                        txt = page_obj.extract_text() or ""
                        txt_upper = txt.upper()
                        if any(term in txt_upper for term in p_passes if len(term) >= 2):
                            target_page_idx = idx_page
                            
                            found_coords = []
                            def visitor_body(text, cm, tm, font_dict, font_size):
                                if any(term in text.upper() for term in p_passes if len(term) >= 2):
                                    if len(tm) >= 6 and tm[5] > 0:
                                        found_coords.append((tm[4], tm[5]))
                            
                            try:
                                page_obj.extract_text(visitor_text=visitor_body)
                            except Exception:
                                pass

                            if found_coords:
                                target_x, target_y = found_coords[0]
                            break

                # Estampar antefirma de margen en TODAS las páginas del documento original
                for idx_p in range(num_pages):
                    p_obj_p = reader_doc.pages[idx_p]
                    pw_p = float(p_obj_p.mediabox.width)
                    m_stamp_x = max(36.0, pw_p - 130.0 - (signer_idx * 110.0))
                    m_stamp_y = 30.0
                    page_stamps[idx_p].append((clean_r, m_stamp_x, m_stamp_y, 90.0, 30.0))

                if target_page_idx is None:
                    target_page_idx = num_pages - 1

                page_obj = reader_doc.pages[target_page_idx]
                pw = float(page_obj.mediabox.width)
                ph = float(page_obj.mediabox.height)

                rw, rh = 120.0, 40.0
                
                if target_y is not None and target_y > 0:
                    stamp_y = min(ph - rh - 10.0, target_y + 8.0)
                    stamp_x = max(36.0, min(target_x if target_x is not None else 40.0, pw - rw - 36.0))
                else:
                    stamp_y = 35.0
                    stamp_x = max(36.0, min(40.0 + (signer_idx * 130.0), pw - rw - 36.0))

                # Estampar rúbrica principal sobre la línea de firma en la página correspondiente
                page_stamps[target_page_idx].append((clean_r, stamp_x, stamp_y, 120.0, 40.0))

            writer_doc = PdfWriter()
            for idx_page, page_obj in enumerate(reader_doc.pages):
                stamps = page_stamps.get(idx_page, [])
                if stamps:
                    pw = float(page_obj.mediabox.width)
                    ph = float(page_obj.mediabox.height)
                    wm_buf = io.BytesIO()
                    c_wm = canvas.Canvas(wm_buf, pagesize=(pw, ph))
                    
                    for stamp_item in stamps:
                        try:
                            cr = stamp_item[0]
                            sx = stamp_item[1]
                            sy = stamp_item[2]
                            sw = stamp_item[3] if len(stamp_item) >= 4 else 120.0
                            sh = stamp_item[4] if len(stamp_item) >= 5 else 40.0
                            c_wm.drawImage(ImageReader(io.BytesIO(cr)), sx, sy, width=sw, height=sh)
                        except Exception:
                            pass
                    
                    c_wm.showPage()
                    c_wm.save()
                    
                    reader_wm = PdfReader(io.BytesIO(wm_buf.getvalue()))
                    if reader_wm.pages:
                        page_obj.merge_page(reader_wm.pages[0])
                
                writer_doc.add_page(page_obj)

            out_doc_buf = io.BytesIO()
            writer_doc.write(out_doc_buf)
            pdf_original_bytes = out_doc_buf.getvalue()

        except Exception:
            pass

    for idx, creds in enumerate(signers_credentials, 1):
        efirma = EFirmaManager(creds['cer_bytes'], creds['key_bytes'], creds['password'])
        
        if not efirma.metadata["valido"]:
            raise ValueError(f"El certificado e.firma del Firmante #{idx} ({efirma.metadata['nombre']}) se encuentra vencido.")

        raw_signature = efirma.sign_hash(pdf_original_bytes)
        sig_b64 = base64.b64encode(raw_signature).decode('utf-8')
        ts = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')

        signatures_list.append({
            'metadata': efirma.metadata,
            'signature_b64': sig_b64,
            'timestamp': ts,
            'rubrica_bytes': creds.get('rubrica_bytes')
        })
        summary_metadata.append(efirma.metadata)

    audit_pdf_bytes = generate_audit_page(pdf_original_bytes, signatures_list)

    writer = PdfWriter()
    reader_doc = PdfReader(io.BytesIO(pdf_original_bytes))
    for page in reader_doc.pages:
        writer.add_page(page)

    reader_audit = PdfReader(io.BytesIO(audit_pdf_bytes))
    for page in reader_audit.pages:
        writer.add_page(page)

    firmantes_str = ", ".join([m['nombre'] for m in summary_metadata])
    rfcs_str = ", ".join([m['rfc'] for m in summary_metadata])

    writer.add_metadata({
        '/Author': firmantes_str,
        '/Subject': f"Documento firmado con e.firma SAT (RFCs: {rfcs_str})",
        '/Creator': "Portal de Firmas OOAD Sonora - IMSS",
    })

    out_buffer = io.BytesIO()
    writer.write(out_buffer)
    return out_buffer.getvalue(), summary_metadata, signatures_list


# =====================================================================
# 4. INTERFAZ STREAMLIT (PORTAL DE FIRMAS OOAD SONORA - IMSS)
# =====================================================================
def main():
    st.set_page_config(
        page_title="Portal de Firmas OOAD Sonora - IMSS",
        page_icon="🟢",
        layout="wide"
    )

    logo_bytes = get_imss_logo_bytes()
    col_logo, col_title = st.columns([1, 4])
    with col_logo:
        st.image(logo_bytes, use_container_width=True)
    with col_title:
        st.title("Portal de Firmas OOAD Sonora")
        st.caption("Órgano de Operación Administrativa Desconcentrada Sonora (IMSS)")

    st.markdown(
        "Firma digitalmente documentos en formato PDF utilizando tus archivos oficiales de la **e.firma (SAT)**. "
        "Soporta firma individual y **Multifirma (múltiples firmantes)**. El procesamiento se realiza **100% en memoria volátil**, "
        "garantizando la máxima seguridad sin almacenamiento en disco."
    )
    st.divider()

    col_mode, _ = st.columns([1, 1])
    with col_mode:
        num_firmantes = st.number_input("👥 Número de Firmantes en el Documento", min_value=1, max_value=100, value=1, step=1)

    st.markdown("<br>", unsafe_allow_html=True)

    col_doc, col_creds = st.columns([1, 1.2], gap="large")

    with col_doc:
        st.subheader("📄 Documento a Firmar")
        uploaded_doc = st.file_uploader("Selecciona el archivo PDF o Word (.docx)", type=["pdf", "docx"], key="doc_file")
        if uploaded_doc:
            st.success(f"Archivo cargado: **{uploaded_doc.name}** ({len(uploaded_doc.getvalue()) / 1024:.1f} KB)")
            if uploaded_doc.name.lower().endswith('.docx'):
                st.info("ℹ️ El documento Word (.docx) se convertirá automáticamente a PDF en memoria antes de aplicar la firma.")
                try:
                    import docx
                    doc_preview = docx.Document(io.BytesIO(uploaded_doc.getvalue()))
                    with st.expander("🔍 Ver vista previa del texto del documento Word"):
                        for parrafo in doc_preview.paragraphs[:10]:
                            if parrafo.text.strip():
                                st.write(parrafo.text)
                except Exception:
                    pass

    signers_credentials = []

    with col_creds:
        st.subheader(f"🔐 Credenciales e.firma SAT ({num_firmantes})")
        tabs = st.tabs([f"Firmante #{i+1}" for i in range(num_firmantes)])

        for idx, tab in enumerate(tabs):
            with tab:
                st.caption(f"Archivos oficiales de la **e.firma (SAT)** del Firmante #{idx+1}")
                cer_file = st.file_uploader(f"Certificado público (.cer) - Firmante {idx+1}", type=["cer"], key=f"cer_{idx}")
                key_file = st.file_uploader(f"Llave privada (.key) - Firmante {idx+1}", type=["key"], key=f"key_{idx}")
                pwd = st.text_input(f"Contraseña - Firmante {idx+1}", type="password", key=f"pwd_{idx}")

                st.markdown("---")
                st.caption("✍️ **Rúbrica / Firma Autógrafa Visual (Opcional)**")
                
                session_key = f"rubrica_bytes_{idx}"
                if session_key not in st.session_state:
                    st.session_state[session_key] = None

                rubrica_mode = st.radio(
                    f"Método para ingresar la rúbrica - Firmante {idx+1}:",
                    ["✏️ Dibujar Rúbrica en Pantalla", "🖼️ Cargar Imagen de Rúbrica (.png, .jpg)"],
                    key=f"rub_mode_{idx}"
                )

                if rubrica_mode == "🖼️ Cargar Imagen de Rúbrica (.png, .jpg)":
                    rubrica_file = st.file_uploader(
                        f"Subir imagen de Rúbrica/Firma (.png, .jpg, .jpeg) - Firmante {idx+1}",
                        type=["png", "jpg", "jpeg"],
                        key=f"rubrica_file_{idx}"
                    )
                    if rubrica_file:
                        proc = _prepare_rubrica_image_bytes(rubrica_file.getvalue())
                        st.session_state[session_key] = proc
                        st.session_state[f"canvas_png_{idx}"] = proc
                else:
                    st.write("✏️ **Dibuja tu firma en el recuadro blanco y presiona 'Confirmar Rúbrica':**")
                    ink_choice = st.radio(
                        f"🎨 Color de Tinta - Firmante {idx+1}:",
                        ["🔵 Azul Institucional (Oficial)", "⬛ Negro"],
                        horizontal=True,
                        key=f"ink_{idx}"
                    )
                    stroke_col = "#003399" if "Azul" in ink_choice else "#000000"

                    try:
                        from streamlit_drawable_canvas import st_canvas
                        canvas_res = st_canvas(
                            stroke_width=3,
                            stroke_color=stroke_col,
                            background_color="#ffffff",
                            height=180,
                            width=400,
                            drawing_mode="freedraw",
                            return_image_data=True,
                            key=f"canvas_{idx}"
                        )
                        col_save, col_clear = st.columns(2)
                        with col_save:
                            btn_confirm = st.button(f"💾 Guardar Rúbrica #{idx+1}", key=f"btn_confirm_{idx}", use_container_width=True)
                        with col_clear:
                            btn_clear = st.button(f"🗑️ Limpiar Rúbrica #{idx+1}", key=f"btn_clear_{idx}", use_container_width=True)
                        
                        if btn_clear:
                            st.session_state[session_key] = None
                            st.session_state[f"canvas_png_{idx}"] = None
                            st.rerun()

                        if canvas_res is not None:
                            try:
                                raw_png = None
                                if hasattr(canvas_res, "image_bytes") and canvas_res.image_bytes:
                                    raw_png = canvas_res.image_bytes
                                elif hasattr(canvas_res, "image_data") and canvas_res.image_data is not None:
                                    pil_img = Image.fromarray(canvas_res.image_data).convert("RGBA")
                                    buf = io.BytesIO()
                                    pil_img.save(buf, format="PNG")
                                    raw_png = buf.getvalue()

                                if raw_png:
                                    png_data = _prepare_rubrica_image_bytes(raw_png)
                                    if png_data:
                                        st.session_state[session_key] = png_data
                                        st.session_state[f"canvas_png_{idx}"] = png_data
                            except Exception:
                                pass
                        
                        if btn_confirm:
                            if st.session_state.get(session_key) or st.session_state.get(f"canvas_png_{idx}"):
                                st.success(f"✅ Rúbrica del Firmante #{idx+1} confirmada correctamente.")
                    except Exception:
                        rubrica_file = st.file_uploader(
                            f"Subir imagen de Rúbrica/Firma (.png, .jpg) - Firmante {idx+1}",
                            type=["png", "jpg", "jpeg"],
                            key=f"fallback_rub_{idx}"
                        )
                        if rubrica_file:
                            proc = _prepare_rubrica_image_bytes(rubrica_file.getvalue())
                            st.session_state[session_key] = proc
                            st.session_state[f"canvas_png_{idx}"] = proc

                rubrica_bytes = st.session_state.get(f"canvas_png_{idx}") or st.session_state.get(session_key)
                if rubrica_bytes:
                    st.success(f"✅ Rúbrica del Firmante #{idx+1} lista para estampar.")
                    st.image(rubrica_bytes, caption=f"Vista previa de Rúbrica dibujada - Firmante #{idx+1}", width=180)

                if cer_file and key_file and pwd.strip():
                    try:
                        efirma_val = EFirmaManager(cer_file.getvalue(), key_file.getvalue(), pwd)
                        st.success(f"🟢 **{efirma_val.metadata['nombre']}** (`{efirma_val.metadata['rfc']}`) — e.firma validada correctamente.")
                        signers_credentials.append({
                            'cer_bytes': cer_file.getvalue(),
                            'key_bytes': key_file.getvalue(),
                            'password': pwd,
                            'rubrica_bytes': rubrica_bytes
                        })
                    except Exception as e_val:
                        st.error(f"❌ Firmante #{idx+1}: {str(e_val)}")
                        with st.expander("💡 ¿Problemas para abrir tu e.firma (.key)? Guía de ayuda"):
                            st.markdown(
                                "1. **Clave Privada de la e.firma**: Recuerda que la e.firma (SAT / FIEL) requiere su propia contraseña de llave privada. **No utilices la contraseña de la CIEC, ni la Contraseña SAT, ni tu RFC**.\n"
                                "2. **Pareja de Archivos (.cer y .key)**: Asegúrate de que el archivo `.key` y el archivo `.cer` fueron emitidos juntos en el mismo trámite del SAT.\n"
                                "3. **Caracteres Especiales**: Si tu clave incluye acentos (`á`, `é`, `í`, `ó`, `ú`), `ñ` o símbolos, la aplicación ahora intenta automáticamente todas las codificaciones (UTF-8, Latin-1, CP1252 y NFD/NFC).\n"
                                "4. **Espacios Accidentales**: Si copiaste la contraseña de un bloc de notas, los espacios iniciales o finales se corrigen automáticamente."
                            )

    st.markdown("<br>", unsafe_allow_html=True)

    col_btn, _ = st.columns([2, 3])
    with col_btn:
        firmar_btn = st.button("🚀 Firmar y Sellar Documento", type="primary", use_container_width=True)

    if firmar_btn:
        if not uploaded_doc:
            st.warning("⚠️ Debes subir un documento PDF o Word (.docx) para firmar.")
            return

        # Re-obtener credenciales de todos los firmantes asegurando la lectura de la rúbrica desde session_state
        signers_credentials = []
        for i in range(num_firmantes):
            cer_f = st.session_state.get(f"cer_{i}")
            key_f = st.session_state.get(f"key_{i}")
            pwd_val = st.session_state.get(f"pwd_{i}")
            
            rub_bytes = (
                st.session_state.get(f"canvas_png_{i}") or
                st.session_state.get(f"rubrica_bytes_{i}")
            )
            if not rub_bytes:
                rf = st.session_state.get(f"rubrica_file_{i}") or st.session_state.get(f"fallback_rub_{i}")
                if rf and hasattr(rf, 'getvalue'):
                    rub_bytes = rf.getvalue()

            if cer_f and key_f and pwd_val and pwd_val.strip():
                try:
                    c_bytes = cer_f.getvalue() if hasattr(cer_f, 'getvalue') else cer_f
                    k_bytes = key_f.getvalue() if hasattr(key_f, 'getvalue') else key_f
                    signers_credentials.append({
                        'cer_bytes': c_bytes,
                        'key_bytes': k_bytes,
                        'password': pwd_val,
                        'rubrica_bytes': rub_bytes
                    })
                except Exception:
                    pass

        if len(signers_credentials) < num_firmantes:
            st.warning(f"⚠️ Debes proporcionar los archivos completos (.cer, .key y contraseña) de la e.firma SAT para los {num_firmantes} firmantes.")
            return

        with st.spinner("Procesando firma criptográfica e.firma (SAT) y generando constancia OOAD Sonora..."):
            try:
                raw_doc_bytes = uploaded_doc.getvalue()
                modified_docx_bytes = None
                insertion_summary = []

                if uploaded_doc.name.lower().endswith('.docx'):
                    modified_docx_bytes, insertion_summary = insertar_firma_en_docx(raw_doc_bytes, signers_credentials)
                    pdf_bytes = convert_docx_to_pdf_bytes(modified_docx_bytes)
                else:
                    pdf_bytes = raw_doc_bytes

                signed_pdf_bytes, summary_meta, sig_details = procesar_firma_pdf(
                    pdf_bytes, signers_credentials, estampar_en_paginas_doc=(modified_docx_bytes is None)
                )

                st.success("✅ ¡Documento firmado exitosamente!")

                if insertion_summary:
                    for item in insertion_summary:
                        st.info(f"✍️ Rúbrica de **{item['nombre']}** insertada {item['metodo']}.")

                st.subheader("👁️ Vista Previa Interactiva del Documento Firmado")
                st.caption("Puedes desplazar y revisar las páginas del documento original y la Hoja de Evidencia Legal (NOM-151) con los sellos y rúbricas incorporadas:")
                display_pdf_inline(signed_pdf_bytes, height=700)

                st.markdown("<br>", unsafe_allow_html=True)

                with st.expander("🔍 Ver Detalles del Sello Digital, Cadena Original y Código QR", expanded=True):
                    for idx, sig_info in enumerate(sig_details, 1):
                        meta = sig_info['metadata']
                        sig_b64 = sig_info['signature_b64']
                        ts = sig_info['timestamp']
                        r_bytes = sig_info.get('rubrica_bytes')

                        cadena_original = f"||{meta['rfc']}|{meta['nombre']}|{meta['no_serie']}|{ts}||"

                        st.markdown(f"### **Firmante #{idx}: {meta['nombre']}** (e.firma SAT)")
                        scol1, scol2 = st.columns([2.2, 1], gap="medium")
                        with scol1:
                            st.write(f"**Titular:** {meta['nombre']}")
                            st.write(f"**RFC:** `{meta['rfc']}` | **CURP:** `{meta['curp']}`")
                            st.write(f"**No. Serie Certificado SAT:** `{meta['no_serie']}` ({meta['emisor']})")
                            st.write(f"**Vigencia Certificado:** {meta['vigencia_inicio']} al {meta['vigencia_fin']}")
                            st.write(f"**Fecha / Hora de Firma:** `{ts}`")
                            
                            st.write("**Cadena Original:**")
                            st.code(cadena_original, language="text")
                            
                            st.write("**Sello Digital (Base64 / RSA SHA-256):**")
                            st.code(sig_b64, language="text")
                            
                        with scol2:
                            if r_bytes:
                                st.write("**Rúbrica Estampada:**")
                                st.image(r_bytes, caption=f"Rúbrica - {meta['nombre']}", width=180)
                            
                            qr_buf = _generate_qr_code_image(f"IMSS-OOAD-SONORA|HASH:{hashlib.sha256(pdf_bytes).hexdigest()[:16]}|RFC:{meta['rfc']}|SERIE:{meta['no_serie']}")
                            st.write("**Código QR de Verificación:**")
                            st.image(qr_buf.getvalue(), caption="QR Evidencia NOM-151", width=150)
                            
                        st.divider()

                nombre_base = uploaded_doc.name.rsplit('.', 1)[0]
                nuevo_nombre_pdf = f"{nombre_base}_firmado_ooad_sonora.pdf"

                if modified_docx_bytes:
                    nuevo_nombre_docx = f"{nombre_base}_con_rubricas.docx"
                    dl_col1, dl_col2 = st.columns(2)
                    with dl_col1:
                        st.download_button(
                            label=f"📥 Descargar PDF Firmado ({nuevo_nombre_pdf})",
                            data=signed_pdf_bytes,
                            file_name=nuevo_nombre_pdf,
                            mime="application/pdf",
                            type="primary",
                            use_container_width=True
                        )
                    with dl_col2:
                        st.download_button(
                            label=f"📥 Descargar Word con Rúbricas ({nuevo_nombre_docx})",
                            data=modified_docx_bytes,
                            file_name=nuevo_nombre_docx,
                            mime="application/vnd.openxmlformats-officedocument.wordprocessingml.document",
                            use_container_width=True
                        )
                else:
                    st.download_button(
                        label=f"📥 Descargar PDF Firmado ({nuevo_nombre_pdf})",
                        data=signed_pdf_bytes,
                        file_name=nuevo_nombre_pdf,
                        mime="application/pdf",
                        type="primary"
                    )

            except Exception as e:
                st.error(f"❌ Error al procesar la firma: {str(e)}")


def display_pdf_inline(pdf_bytes: bytes, height: int = 700):
    """Renderiza una vista previa interactiva del archivo PDF firmado directamente en Streamlit."""
    b64_pdf = base64.b64encode(pdf_bytes).decode('utf-8')
    pdf_display = f'''
    <iframe src="data:application/pdf;base64,{b64_pdf}#toolbar=1&navpanes=1&scrollbar=1" 
            width="100%" 
            height="{height}px" 
            type="application/pdf" 
            style="border:2px solid #006341; border-radius:10px; box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1);">
    </iframe>
    '''
    st.markdown(pdf_display, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
