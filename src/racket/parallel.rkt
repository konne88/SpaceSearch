#lang racket

(require "extraction.rkt" "worker.rkt")

(require racket/place)
(require racket/place/distributed)
(require racket/serialize)

(provide place-pool run-worker)

(define (forever f) (f) (forever f))

(define (cpus)
  (match-let ([(list out in pid err ctrl) (process "nproc")])
    (ctrl 'wait)
    (define res (read-line out))
    (close-output-port in)
    (close-input-port out)
    (close-input-port err)
    (stream->list (in-range (string->number res)))))

(define (nodes)
  (define evars (environment-variables-names (current-environment-variables)))
  (append* (list "localhost") (for/list ([evar evars])
    (define r (regexp-match #rx"^([^_]+)_NAME$" evar))
    (if r (list (string-downcase (bytes->string/utf-8 (second r)))) '()))))

(define (run-worker ch)
  (define info (deserialize (place-channel-get ch)))
  (define cpu (first info))
  (define node (second info))
  (define worker (third info))
  (define task (fourth info))
  (printf "# place received task and worker at ~a on cpu ~a\n" node cpu)
  (flush-output)
  (define result (@ denoteWorker worker task))
  (place-channel-put ch (serialize result))
  (printf "# place done at ~a on cpu ~a\n" node cpu)
  (flush-output))

(define (place-pool)
  (define task-queue (make-channel))
  (define thd (current-thread))
  (define count 0)
  (define nodes* (nodes))
  (define cpus* (cpus))
  (write-string (string-append "nodes: " (~a nodes*) "\n"))
  (write-string (string-append "cpus: " (~a cpus*) "\n"))
  (flush-output)
 
  ; start threads/nodes
  (for*/list ([node nodes*] [cpu cpus*])
    (thread (lambda ()
      (write-string (string-append "# node at " (~a node) " on cpu " (~a cpu) "\n"))
      (flush-output)
      (define nd (create-place-node node #:listen-port (+ 1234 cpu)))
      (forever (lambda ()
        (define workerTask (deserialize (channel-get task-queue)))
        (define ch (dynamic-place #:at nd (quote-module-path) 'run-worker))
        (place-channel-put ch (serialize (append (list cpu node) workerTask)))
        (define result (deserialize (place-channel-get ch)))
        (thread-send thd result))))))

  ; return enqueue task function
  (lambdas (worker task)
    (set! count (+ count 1))
    (printf "# checking task ~a at time ~a\n" count (current-seconds))
    (flush-output)
    (channel-put task-queue (serialize (list worker task)))
    (lambda () (thread-receive))))

