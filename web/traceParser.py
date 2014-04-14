import json

class TraceParser :

    def __init__ (self) :
        self.steps = []

    def fromJsonString (self, jsonString) :
        self.steps = json.loads(jsonString)

    def fromFile (self, filename) :
        fh = open(filename, 'rb')
        jsonRaw = fh.read()
        fh.close()

        self.fromJsonString(jsonRaw)