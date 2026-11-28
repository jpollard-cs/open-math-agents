"""Generate the exact integer-grid T-pentomino figure, using only the standard library."""
from pathlib import Path
from xml.sax.saxutils import escape

prefix=['<svg xmlns="http://www.w3.org/2000/svg" width="870" height="315" viewBox="0 0 870 315">',
'<rect width="870" height="315" fill="#faf8f4"/>',
'<defs><clipPath id="crop"><rect width="252" height="180"/></clipPath></defs>']
end=[]
for n,(title,word,caption) in enumerate([
    ('One copy',[1],'Constant row increment +1'),
    ('Three copies',[1,1,-1],'Repeating row increments +1, +1, −1'),
    ('No second period',[1 if j.bit_count()%2==0 else -1 for j in range(32)],'A window of the Thue–Morse sequence')]):
    ox=18+n*288
    def label(y,value,size,color):
        return f'<text x="{ox}" y="{y}" font-family="sans-serif" font-size="{size}" fill="{color}">{escape(value)}</text>'
    end.append(label(38,title,20,'#18353b'))
    end.append(f'<g transform="translate({ox} 55)" clip-path="url(#crop)">')
    end.append('<rect width="252" height="180" fill="#e9e2d5"/>')
    colors=['#34687a','#bf7155','#5e8774','#786b89']
    phase=0
    for j in range(8):
        for i in range(-1,7):
            x=(3*i+phase)*15
            y=(2*j-2)*15
            color=colors[(i+2*j)%len(colors)]
            # Single polygon is the union of the five unit cells.
            path='M0 0h15v15h30v15H15v15H0z'
            end.append(f'<path transform="translate({x} {y})" d="{path}" fill="{color}" stroke="#fffaf0" stroke-width="1"/>')
        phase=(phase+word[j%len(word)])%3
    end+=['</g>',label(259,caption,12,'#243d40')]
end.append('<text x="18" y="296" font-size="15" font-family="sans-serif" fill="#243d40">Each packing covers five sixths of the grid. Cream cells remain uncovered.</text>')
Path('t-periods.svg').write_text('\n'.join(prefix+end+['</svg>'])+'\n')
