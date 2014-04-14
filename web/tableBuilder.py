
class TableBuilder :
    
    def __init__ (self, columnTitles) :
        self.columnTitles = columnTitles
        self.rows = []

    def addRow (self, row) :
        self.rows.append(row)

    def build (self) :
        html = '<table><tr>'
        for title in self.columnTitles :
            html += '<td><strong>' + title + '</strong></td>'
        html += '</tr>'
        html += '\n'.join(map(lambda row: '<tr>' + ''.join(map(lambda column: '<td class="tdcontent">' + column + '</td>', row)) + '</tr>', self.rows))
        return html + '</table>'