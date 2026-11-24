// Prints the path of each C# file under a directory as soon as macOS says it
// changed (FSEvents), one per line: what `hot.py` waits on instead of
// walking the project, which takes a second where the art is.
//
// swiftc -O -o fsevents fsevents.swift && ./fsevents <directory>
import CoreServices
import Foundation

setvbuf(stdout, nil, _IOLBF, 0)
let root = CommandLine.arguments.count > 1 ? CommandLine.arguments[1] : "."

let callback: FSEventStreamCallback = { _, _, count, paths, _, _ in
    let list = unsafeBitCast(paths, to: NSArray.self)
    for index in 0..<count {
        if let path = list[index] as? String, path.hasSuffix(".cs") {
            print(path)
        }
    }
}

var context = FSEventStreamContext()
let flags = kFSEventStreamCreateFlagFileEvents | kFSEventStreamCreateFlagUseCFTypes | kFSEventStreamCreateFlagNoDefer
guard let stream = FSEventStreamCreate(
    nil, callback, &context, [root] as CFArray,
    FSEventStreamEventId(kFSEventStreamEventIdSinceNow), 0.01, FSEventStreamCreateFlags(flags))
else {
    FileHandle.standardError.write("cannot watch \(root)\n".data(using: .utf8)!)
    exit(1)
}
FSEventStreamSetDispatchQueue(stream, DispatchQueue.main)
FSEventStreamStart(stream)
dispatchMain()
