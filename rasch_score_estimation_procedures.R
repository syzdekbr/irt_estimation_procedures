
###*** RASCH ABILITY ESTIMATION PROCEDURES

# Basic estimates ---------------------------------------------------------

## Estimation Procedures mostly from Wright, B. & Stone, M. (1979)

## Use a vector of difficulties like
difficulties <- c(-6.2, -4.11, -2.58, -2.76, -4.34, -2.58, -2.06, -2.06, -1.03, -.12, -.85, -.52, 
                 -1.51, -.77, 1.93, 1.36, 2.01, 2.88, 3.33, 3.33, 4.52, 6.27, 5.81)

## PROX- if difficulties are normally distributed
prox_estimation <- function(difficulties, raw_score){
  variance <- {(sum(difficulties^2) - length(difficulties)*mean(difficulties)^2)/
      (length(difficulties) -1)}
  height <- mean(difficulties)
  tibble::tibble(
    prox_estimate = height + sqrt(1 + (variance/2.89)) * log(raw_score/(length(difficulties) - raw_score)),
    prox_se = sqrt(1 + variance/2.89)*(sqrt((length(difficulties)/(raw_score*(length(difficulties) - raw_score)))))
  )
}

## UCON
# first esimate of b
ucon_estimation <- function(difficulties, raw_score){
  b <- -10
  # new_b <- log((raw_score/length(difficulties)/(1 - (raw_score/length(difficulties)))))
  new_b <- log(raw_score / (length(difficulties) - raw_score))
  while(abs(new_b - b) > .01){
    b <- new_b
    prob <- (exp(b - difficulties))/(1 + exp(b - difficulties))
    new_b <- b + (raw_score - sum(prob))/(sum(prob*(1-prob)))
  }
  tibble::tibble(
    ucon_estimate = new_b, 
    ucon_se = (sum(prob*(1-prob))^-(1/2))
    )
}

##UFORM
uform_estimation <- function(difficulties, raw_score){
difficulties_tibble <- tibble::tibble(difficulties)
  w <- {((sum(dplyr::pull(dplyr::slice_max(difficulties_tibble, order_by = difficulties, n = 2)))-
      sum(dplyr::pull(dplyr::slice_min(difficulties_tibble, order_by = difficulties, n = 2))))/2)*
      (length(difficulties)/(length(difficulties) - 2))
  }
  f <- raw_score / length(difficulties)
  h <- sum(difficulties)/ length(difficulties)
  A <- 1 - exp(-w*f)
  B <- 1 - exp(-w*(1-f))
  C <- 1 - exp(-w)
  b <- h + w*(f - .5) + log(A/B)
  tibble::tibble(
    uform_estimate = b,
    uform_se = ((w/length(difficulties))*(C/(A*B)))
  )
}

# AMLE- Procedure is to iterate through, pick a new ability score that reduces distance 
# between difficulties and that ability, calculate the variance, and reduce this variance
amle_estimation <- function(difficulties, raw_score){
  d_mean <- mean(difficulties)
  variance <- sum((difficulties - d_mean)^2)/(length(difficulties) - 1)
  # First estimate uses PROX, from above functions
  m <- prox_estimation(difficulties, raw_score)$prox_estimate
  m1 <- -10 # Arbitrary starting point
  while(abs(m1-m) > .01){
    prob <- 1/(1+ exp(difficulties - m)) # probability of success
    score <- sum(prob)
    # Recalculate variance with new estimate of m
    variance <- sum((difficulties - m)^2)/(length(difficulties) - 1)
    m1 <- m + (raw_score - score)/variance
    variance <- sum((difficulties - m1)^2)/(length(difficulties) - 1)
    m2 <- m1 + (raw_score - score)/variance
    # variance <- sum((exp(m - difficulties))/(1+ exp((m-difficulties)^2)))
    variance <- ifelse(abs(m1 - m) > abs(m2 - m),
                      max(variance*2, 1.0),
                      variance)
    m2 <- m
    m <- m1
  }
  ## Warm MLE estimation to correct for bias
  j <- sum(prob*(1-prob)*(1-2*prob))
  i <- sum(prob*(1-prob))
  warm_mle <- m1 + (j/(2*(i^2)))
  tibble::tibble(
    amle_estimate = m1,
    amle_se = sqrt(1/variance),
    warm_mle_estimate = warm_mle
  )
}

# Procedure for EAP to MLE estimation- EAP -------------------------------------
## From Irtoys: https://github.com/cran/irtoys

###*** EAP first, when responses all 0 or 1

## Normal quadrature
normal.qu = function(
    Q = 15, # Number of quadrature points to be selected
    lower=-4, # Boundaries
    upper=4, 
    mu=0, # mean and Sd
    sigma=1,
    scaling="points") # Quadrature points rescaled
  {
  if (upper<=lower || sigma<=0 || Q<3) stop("bad argument")
  # Q quadrature points evenly distributed between boundaries
  qp=seq(lower,upper,length.out = Q)

  if(scaling=="points") {
    # Should always be this condition, rather than "else"
    qw=dnorm(qp,mean = 0, sd = 1) # Probability density standard normal
    qw=qw/sum(qw) # For qw to add up to unity
    qp=qp*sigma+mu # Returns qp for standard normal
  } else {
    # Only useful for another value of mu, sigma other than 0, 1
    qw=dnorm(qp,mu,sigma)
    qw=qw/sum(qw)
  }
  # A list of probabilities (quad.weights) of quad.points
  return(list(quad.points=qp, quad.weights=qw))
}

log_likelihood_function = function(
    qp, # Quadrature points
    r, # Response matrix
    p, # Rasch parameters
    mu,
    sigma,
    method = "ML") # Maximum likelihood
  {
  # Calculate probabilities, generalized here for multiple parameter IRT, but Rasch parameters
  # will condense to Rasch model
  pr = p[,3] + (1.0 - p[,3])/(1.0 + exp(p[,1]*(p[,2] - qp)))
  # Get maximimum and minimum probabilities or defined max min
  pr = pmax(pr, .00001); pr = pmin(pr, .99999)
  # Log likelihood- response_vector time log probabilities plus variance
  ll = r*log(pr) + (1-r)*log(1.0-pr)
  lf = sum(ll)
  if (method != "ML") lf = lf + log(dnorm(qp,mu,sigma)) 
  return(lf)
} 

eap.one = function(r, p, qp, qw) {
  # Remove na values from response matrix and probabilities
  cc = !is.na(r)
  r  = r[cc]
  p  = p[cc,,drop=FALSE]
  n  = length(r)
  if (n < 1) return(c(NA, NA, 0))
  ll = sapply(qp, log_likelihood_function, r=r, p=p, mu=NULL, sigma=NULL, method="ML")
  # Weighted loglikelihood
  wl = exp(ll)*qw
  swl = sum(wl)
  # Standardized weighted likelihood quad points
  x  = sum(wl*qp)/swl
  # Deviance
  dev = qp - x
  sem = sqrt(sum(wl*dev*dev)/swl)
  return(c(x,sem,n))
}

eap = function(resp, ip, qu) {
  if (is.list(ip)) ip = ip$est
  if (is.null(dim(resp))) dim(resp) = c(1,length(resp))
  # Error handling
  if (is.null(dim(ip))) stop("item parameters not a matrix")
  if (nrow(ip) != ncol(resp)) stop("responses - item parameters mismatch")
  np = nrow(resp)
  qp = qu$quad.points
  qw = qu$quad.weights
  o  = sapply(1:np, function(i) eap.one(r=resp[i,], p=ip, qp, qw),USE.NAMES=FALSE)
  rownames(o) = c("est","sem","n")
  return(t(o))
}

# Define the Rasch parameters. Will be a L x 3 matrix. Column 1 is a, discrimination, is L
# length vector of 1. Column 2 is difficulties, passed to list, Column 3 is c, set to 0.

# Function that takes difficulties and response vector and returns EAP theta and sem

eap_estimation_func <- function(difficulties, response_vector){
item_parameters<- list(
  est = matrix(
    c(rep(1,length(difficulties)), # a
      difficulties, # b
      rep(0,length(difficulties))), # c
    ncol = 3
    )
  )

response_matrix <- matrix(
  response_vector, nrow = 1
  )

eap(resp = response_matrix, ip = item_parameters, qu = normal.qu())
}


# MLE ---------------------------------------------------------------------

###*** MLE- to be used after responses are all not 0 or 1

# Item Response Function, or Item Characteristic Curve; picture logistic curve of response
# for each theta estimate
irf = function(
    ip, # item parameters
    items=NULL,
    x=NULL # Values of latent variable at which will be evaluated, if NULL 99 equal spaces
    # between interval
    ) 
  {
  if (is.null(x)) 
    x = seq(-4, 4, length = 101)
  if (is.list(ip)) ip = ip$est
  if (is.null(dim(ip))) 
    dim(ip) = c(1, 3)
  if (!is.null(items)) ip = ip[items, , drop=FALSE]
  # Returns array  of x by nrow of parameters of x, abilities, subtracted from difficulties
  f = sweep(outer(x, ip[,2], "-"), 2, ip[,1], "*")
  f = 1 / (1 + exp(-f))
  if (any(ip[,3]!=0)) 
    f = sweep(sweep(f, 2, 1-ip[,3], "*"), 2, ip[,3], "+")
  r = list(x = x, f = f)
  class(r) = "irf"
  return(r)
}

# Item Information Function- gets item information for each item, using item response
# function from above; this function used in Test Information Functio below
iif = function(ip, items=NULL, x=NULL) {
  if (is.null(x)) 
    x = seq(-4, 4, length = 101) # Ability interval
  # Check data
  if (is.list(ip)) ip = ip$est
  if (is.null(dim(ip))) 
    dim(ip) = c(1, 3)
  if (!is.null(items)) ip = ip[items, ,drop=FALSE]
  p = irf(ip, items=NULL, x)$f  # Item response function from above
  if (any(ip[, 3] != 0)) {
    ip[,3] = 0
    q = irf(ip, items=NULL, x)$f
    f = q^2*(1-p)/p # standardized probability
  } else 
    f = p*(1-p)
  f = sweep(f, 2, ip[,1]^2, "*")  
  r = list(x = x, f = f)
  class(r) = "iif"
  return(r)
}

# Test Information Function- Applies item information function to items;
# used in mle.one below
tif = function(ip, x=NULL) {
  i = iif(ip=ip, items=NULL, x=x) # item information function above
  if (is.null(dim(i$f))) dim(i$f) = c(length(i$x),length(i$f))
  f = apply(i$f, 1, sum) # apply across columns, down rows
  r = list(x=i$x, f=f, ni=ncol(i$f))
  class(r) = "tif"
  return(r)
}

## Function to conduct maximum likelihood estimation
mle.one = function(
    resp, # response matrix
    ip, # item parameters
    mu=mu, 
    sigma=sigma, 
    method=method) { 
  # Remove na
  cc = !is.na(resp)                                        
  resp = resp[cc]                                          
  ip = ip[cc, , drop=FALSE]                                             
  n = length(resp)                                         
  if (n < 1) return(c(NA, NA, 0))
  # Finds maximum of log-likelihood for given constraints
  est = optimize(log_likelihood_function, lower = -4, upper = 4, maximum = TRUE, 
                 r = resp, p = ip, mu = mu, sigma = sigma, method = method)$maximum
  # Test information function
  ti = tif(ip, est)$f
  if (method != "ML") ti = ti + 1/(sigma * sigma) # ti plus variance
  sem = sqrt(1/ti)
  return(c(est, sem, n))
}

## Checks data and applies mle.one function, returns estimate, sem, and n
mlebme = function(resp, ip, mu=0, sigma=1, method="ML") {
  # Check for invalid data
  if (is.list(ip)) ip = ip$est
  if (is.null(dim(resp))) dim(resp) = c(1,length(resp))
  if (is.null(dim(ip))) stop("item parameters not a matrix")
  if (nrow(ip) != ncol(resp)) stop("responses - item parameters mismatch")
  np = nrow(resp)
  # Apply mle.one
  o = sapply(1:np, function(i) mle.one(resp=resp[i,], 
                                       ip=ip, mu=mu, sigma=sigma, method=method))
  rownames(o) = c("est","sem","n")
  return(t(o)) 
}

## Prepares data to apply above mlebme function
mle_estimation_func <- function(difficulties, response_vector){
  # Convert rasch difficulties to matrix, which function requires
  item_parameters<- list(
    est = matrix(
      c(rep(1,length(difficulties)), # a- in Rasch all 1's
        difficulties, # b
        rep(0,length(difficulties))), # c- in Rasch all 0's
      ncol = 3
    )
  )
  # Convert response_vector to matrix, which function requires
  response_matrix <- matrix(
    response_vector, nrow = 1
  )
  mlebme(resp = response_matrix, ip = item_parameters)
}

# EAP and MLE Algorithm ---------------------------------------------------

###*** Integrating above functions into algorithm
## Function to choose between EAP and MLE. Start with EAP until not all 0 or 1, then MLE
apply_estimation_function <- function(set_responses){
  # Check if responses are all either 0 or 1
  if(length(unique(set_responses$responses)) == 1){
    eap_estimation_func(
      difficulties = set_responses$difficulties, 
      response_vector = set_responses$responses
    )
  } else{
    mle_estimation_func(
      difficulties = set_responses$difficulties, 
      response_vector = set_responses$responses
    )
  }
}


## Will apply estimation procedure until cut_score is outside of estimate +/- 95% CI
looping_apply_function <- function(number_of_items, prob_success, cut_score){
  # This is user set information about number of items and success probability
  set_responses <- response_vector_items(number_of_items, prob_success)
  for(n in 1:number_of_items){
    if((cut_score >= tmp$est - 1.65*tmp$sem) & (cut_score <= tmp$est + 1.65*tmp$sem)){
      # Loop through each item in item bank and check if cut_score outside estimate
      tmp <- as.data.frame(apply_estimation_function(set_responses[1:n,]))
    } else{
      tmp
    }
  }
  tmp
}

# Simulation ---------------------------------------------------------

###*** Data for simulating
###* In real use, use Rasch item parameters and candidate response vector
# Rasch model with sample data with persons as rows and items as columns
p.1pl <- irtoys::est(irtoys::Scored, engine = "ltm", model = "1PL", rasch = TRUE)
# Pass difficulties- obtained from researchers
difficulties_items <- tibble::tibble(
  question_number = 1:nrow(p.1pl$est),
  difficulties = p.1pl$est[,2]
)
  
# This is responses of candidate in vector of 0,1 for each item
response_vector_items <- function(number_of_items, prob_success){
  # Creating df with question_number, responses, and difficulties for each item
  dplyr::inner_join(
  tibble::tibble(
    # question_number is unique id. Use whatever we have as id
    question_number = sample(1:nrow(p.1pl$est), number_of_items, replace = F),
    # 0,1 vector. Here sampling according to chosen probabilities
    responses = sample(c(0,1), 
                       size = number_of_items, 
                       prob = c(1-prob_success, prob_success),
                       replace = T)
  ), 
    difficulties_items, # above Rasch estimates
    by = "question_number"
  )
}

## Simulation example
purrr::map(1:10,~{
# Reset tmp df that holds estimation data at beginning of each procedures
tmp <<- tibble::tibble(
  est = -1,
  sem = 1,
  n = 0
)
# Apply function, number_of_items up to number of difficulties, adjust prob and cut_score
# to see if approximates well
looping_apply_function(number_of_items = 15, prob = .9, cut_score = 0)
})
