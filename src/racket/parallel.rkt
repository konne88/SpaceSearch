#lang racket

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction-racket.rkt")
(require (except-in "network/network.rkt" current original path))
(require "config.rkt")
(require "bgpv-core.rkt")
(require "setup.rkt")

(require racket/place)
(require racket/place/distributed)
(require racket/serialize)

(provide place-pool enqueue-task)

(define (run-runnable runnable input)
  (case runnable
    [(bgp-core) (@ bgpCore input)]
    [else (error "unknown runnable"))))

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

(define (place-pool worker)
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
        (define task (channel-get task-queue))
        (define ch (dynamic-place #:at nd (quote-module-path) 'run-worker))
        (place-channel-put ch (serialize cpu))
        (place-channel-put ch (serialize node))
        (place-channel-put ch (serialize worker)
        (place-channel-put ch (serialize task))
        (define result (deserialize (place-channel-get ch)))
        (thread-send thd result)))))))

  ; return initialized state
  (values count task-queue))

(define enqueue-task (lambdas (pool task)
  (define-values (count task-queue) pool)
  (set! count (+ count 1))
  (write-string (string-append "checking " (~a count) " at " (~a (current-seconds)) "\n"))
  (flush-output)
  (channel-put task-queue (serialize task))
  (lambda () (thread-receive))))

(define (run-worker ch)
  (define cpu (deserialize (place-channel-get ch)))
  (define node (deserialize (place-channel-get ch)))
  (define worker (deserialize (place-channel-get ch)))
  (write-string (string-append "# place loaded worker " (~a worker) " at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output)
  (define task (deserialize (place-channel-get ch)))
  (define result (run-runnable worker task))
  (place-channel-put ch (serialize result))
  (write-string (string-append "# place done at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output))




(define distributed-bgpv-scheduler (lambdas (setup query routings)
  (define checks (coq-list-length routings))
  (write-string (string-append "total number of checks " (~a checks) "\n"))
  (flush-output)

  ; provide work for threads
  (define count 0)
  (@ search listSpaceSearch (@ bind listSpaceSearch 
    (coq-list-chunks parallel-batch-size routings) (lambda (sub-routings)
      (define jobs (@ bind listSpaceSearch 
        (coq-list-chunks symbolic-batch-size sub-routings) (lambda
(sub-sub-routings)
          (set! count (+ count symbolic-batch-size))
          (write-string (string-append "checking " (~a count) " of " (~a checks)
" at " (~a (current-seconds)) "\n"))
          (flush-output)
          (channel-put work-queue sub-sub-routings)
          (@ single listSpaceSearch count))))

      (write-string (string-append "collecting " (~a (coq-list-length jobs)) "
results\n"))
      (flush-output)

      ; collect results
      (@ bind listSpaceSearch jobs (lambda (_) (thread-receive))))))))






